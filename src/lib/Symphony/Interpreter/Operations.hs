module Symphony.Interpreter.Operations where

import Symphony.Prelude

import Symphony.Syntax

import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.ReadType
import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Primitives
import Symphony.Interpreter.Error

-----------------
--- Utilities ---
-----------------

bindTo ∷ (STACK) ⇒ Var → v → IM v a → IM v a
bindTo x ṽ = mapEnvL iCxtEnvL ((x ↦ ṽ) ⩌)

bindVal ∷ (STACK, Value v) ⇒ v → Pat → IM v (IM v v → IM v v)
bindVal ṽ ψ = do
  f𝑂 ← unFailT $ matchVal ṽ ψ
  error𝑂 f𝑂 $
    throwIErrorCxt TypeIError "bindVal: ṽ doesn't match ψ" $ frhs
    [ ("ṽ", pretty ṽ)
    , ("ψ", pretty ψ)
    ]

singletonMode ∷ (STACK) ⇒ IM v PrinVal
singletonMode = do
  m ← askL iCxtModeL
  error𝑂 (view (one𝑃L ⊚ addTopL) m) $
    throwIErrorCxt TypeIError "singletonMode: view (one𝑃L ⊚ addTopL) m" $ frhs
    [ ("m", pretty m)
    ]

defaultClearValR ∷ (STACK, Value v) ⇒ Type → ValR v e
defaultClearValR = \case
  BaseT bτ → BaseV $ Clear $ defaultClearBaseVal bτ
  _        → undefined --TODO

------------------------
--- ValR Convenience ---
------------------------

introLoc ∷ (STACK) ⇒ (ℝMut v ∨ 𝕍Mut v) → IM v (ValR v e)
introLoc ℓ = do
  m ← askL iCxtModeL
  return $ LocV m ℓ

elimBase ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (BaseVal e)
elimBase v = error𝑂 (view baseVL v) $
             throwIErrorCxt TypeIError "elimBase: view baseVL v ≡ None" $ frhs
             [ ("v", pretty v)
             ]

elimList ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (𝐿 v)
elimList v = error𝑂 (view listVL v) $
             throwIErrorCxt TypeIError "elimList: view listVL v ≡ None" $ frhs
             [ ("v", pretty v)
             ]

elimClo ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (𝑂 Var ∧ ((IM v v → IM v v) → v → IM v v))
elimClo v = do
  self𝑂 :* fne ← error𝑂 (view cloVL v) $
                 throwIErrorCxt TypeIError "elimClo: view cloVL v ≡ None" $ frhs
                 [ ("v", pretty v)
                 ]
  return $ self𝑂 :* unNoEq fne

elimLocRead ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (ℝMut v ∨ 𝕍Mut v)
elimLocRead v = do
  m      ← askL iCxtModeL
  l :* ℓ ← error𝑂 (view locVL v) $
           throwIErrorCxt TypeIError "elimLocRead: view locVL v ≡ None" $ frhs
           [ ("v", pretty v)
           ]
  guardErr (m ⊑ l) $
    throwIErrorCxt TypeIError "elimLocRead: m ⋢ l" $ frhs
    [ ("m", pretty m)
    , ("l", pretty l)
    ]
  return ℓ

elimLocWrite ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (ℝMut v ∨ 𝕍Mut v)
elimLocWrite v = do
  m      ← askL iCxtModeL
  l :* ℓ ← error𝑂 (view locVL v) $
           throwIErrorCxt TypeIError "elimLocRead: view locVL v ≡ None" $ frhs
           [ ("v", pretty v)
           ]
  guardErr (m ≡ l) $
    throwIErrorCxt TypeIError "elimLocWrite: m ≢ l" $ frhs
    [ ("m", pretty m)
    , ("l", pretty l)
    ]
  return ℓ

elimRef ∷ (STACK, Pretty v) ⇒ ℝMut v ∨ 𝕍Mut v → IM v (ℝMut v)
elimRef 𝓁 = case 𝓁 of
  Inl r  → return r
  Inr _a → throwIErrorCxt TypeIError "elimRef: 𝓁 ≢ ref _" $ frhs
             [ ("𝓁", pretty 𝓁)
             ]

elimArr ∷ (STACK, Pretty v) ⇒ ℝMut v ∨ 𝕍Mut v → IM v (𝕍Mut v)
elimArr 𝓁 = case 𝓁 of
  Inl _r → throwIErrorCxt TypeIError "elimArr: 𝓁 ≢ arr _" $ frhs
             [ ("𝓁", pretty 𝓁)
             ]
  Inr a → return a

elimBundle ∷ (STACK, Pretty v, Pretty e) ⇒ ValR v e → IM v (PrinVal ⇰ v)
elimBundle v = error𝑂 (view bundleVL v) $
               throwIErrorCxt TypeIError "elimBundle: view bundleVL v ≡ None" $ frhs
               [ ("v", pretty v)
               ]

locateValR ∷ (STACK, Value v) ⇒ ValR v e → IM v (ValR v e)
locateValR v = case v of
  BaseV _bv   → return v
  ProdV ṽₗ ṽᵣ → do
    ṽₗˡ ← locateVal ṽₗ
    ṽᵣˡ ← locateVal ṽᵣ
    return $ ProdV ṽₗˡ ṽᵣˡ
  SumV bvₜ ṽₗ ṽᵣ → do
    ṽₗˡ ← locateVal ṽₗ
    ṽᵣˡ ← locateVal ṽᵣ
    return $ SumV bvₜ ṽₗˡ ṽᵣˡ
  ListV ṽs → do
    ṽsˡ ← mapM locateVal ṽs
    return $ ListV ṽsˡ
  CloV _self𝑂 _f → return v
  LocV _m _𝓁 → return v
  BundleV ρtoṽ → do
    ρtoṽˡ ← mapM𝐷 locateVal ρtoṽ
    return $ BundleV ρtoṽˡ
  DefaultV → return v

----------------------------
--- Operations on Values ---
----------------------------

matchLClear ∷ (STACK, Value v) ⇒ BaseVal e → v → Pat → FailT (IM v) (IM v v → IM v v)
matchLClear bvₜ ṽₗ ψₗ = do
  cbvₜ ← abort𝑂 $ view clearL bvₜ
  bₜ   ← lift $ elimBool cbvₜ
  if bₜ then matchVal ṽₗ ψₗ else abort

matchLEnc ∷ (STACK, Value v) ⇒ BaseVal (EBV v) → v → Pat → FailT (IM v) (IM v v → IM v v)
matchLEnc bvₜ ṽₗ ψₗ = do
  ṽₜ ← lift $ introVal $ BaseV bvₜ
  fₗ ← matchVal ṽₗ ψₗ
  return $ \ xM → do
    ṽₗᵒ ← mapEnvL iCxtMPCPathConditionL (ṽₜ :&) $ fₗ xM
    ṽᵣᵒ ← introVal $ DefaultV
    muxVal ṽₜ ṽₗᵒ ṽᵣᵒ

matchRClear ∷ (STACK, Value v) ⇒ BaseVal e → v → Pat → FailT (IM v) (IM v v → IM v v)
matchRClear bvₜ ṽᵣ ψᵣ = do
  cbvₜ ← abort𝑂 $ view clearL bvₜ
  bₜ   ← lift $ elimBool cbvₜ
  if not bₜ then matchVal ṽᵣ ψᵣ else abort

matchREnc ∷ (STACK, Value v) ⇒ BaseVal (EBV v) → v → Pat → FailT (IM v) (IM v v → IM v v)
matchREnc bvₜ ṽᵣ ψᵣ = do
  ṽₜ ← lift $ introVal $ BaseV bvₜ
  negṽₜ ← lift $ primVal NotO $ ṽₜ :& Nil
  fᵣ ← matchVal ṽᵣ ψᵣ
  return $ \ xM → do
    ṽₗᵒ ← introVal $ DefaultV
    ṽᵣᵒ ← mapEnvL iCxtMPCPathConditionL (negṽₜ :&) $ fᵣ xM
    muxVal ṽₜ ṽₗᵒ ṽᵣᵒ

matchVal ∷ (STACK, Value v) ⇒ v → Pat → FailT (IM v) (IM v v → IM v v)
matchVal ṽ = \case
  VarP x → return $ bindTo x ṽ
  BulP → do
    v ← lift $ elimVal ṽ
    abort𝑂 $ view (bulVL ⊚ clearL ⊚ baseVL) v
    return id
  EPrinSetP → do
    v ← lift $ elimVal ṽ
    ρsv ← abort𝑂 $ view (prinSetVL ⊚ clearL ⊚ baseVL) v
    let ρ𝑃 = elimPSV ρsv
    abort𝑂 $ view empty𝑃L ρ𝑃
    return id
  NEPrinSetP x₁ ψ₂ → do
    v ← lift $ elimVal ṽ
    ρsv ← abort𝑂 $ view (prinSetVL ⊚ clearL ⊚ baseVL) v
    let ρ𝑃 = elimPSV ρsv
    ρ :* ρs ← abort𝑂 $ view nonEmpty𝑃L ρ𝑃
    ṽ₁ ← lift $ introVal $ BaseV $ Clear $ PrinV ρ
    ṽ₂ ← lift $ introVal $ BaseV $ Clear $ PrinSetV $ PowPSV ρs
    let f₁ = bindTo x₁ ṽ₁
    f₂ ← matchVal ṽ₂ ψ₂
    return $ compose [ f₂, f₁ ]
  ProdP ψₗ ψᵣ → do
    v ← lift $ elimVal ṽ
    ṽₗ :* ṽᵣ ← abort𝑂 $ view prodVL v
    fₗ ← matchVal ṽₗ ψₗ
    fᵣ ← matchVal ṽᵣ ψᵣ
    return $ compose [ fᵣ, fₗ ]
  LP ψₗ → do
    v ← lift $ elimVal ṽ
    bvₜ :* ṽₗ :* _ṽᵣ ← abort𝑂 $ view sumVL v
    tries [ matchLClear bvₜ ṽₗ ψₗ , matchLEnc bvₜ ṽₗ ψₗ ]
  RP ψᵣ → do
    v ← lift $ elimVal ṽ
    bvₜ :* _ṽₗ :* ṽᵣ ← abort𝑂 $ view sumVL v
    tries [ matchRClear bvₜ ṽᵣ ψᵣ , matchREnc bvₜ ṽᵣ ψᵣ ]
  NilP → do
    v ← lift $ elimVal ṽ
    abort𝑂 $ view (nilL ⊚ listVL) v
    return id
  ConsP ψ₁ ψ₂ → do
    v ← lift $ elimVal ṽ
    ṽ₁ :* ṽs ← abort𝑂 $ view (consL ⊚ listVL) v
    ṽ₂ ← lift $ introVal $ ListV ṽs
    f₁ ← matchVal ṽ₁ ψ₁
    f₂ ← matchVal ṽ₂ ψ₂
    return $ compose [ f₂, f₁ ]
  EBundleP → do
    v ← lift $ elimVal ṽ
    abort𝑂 $ view (empty𝐷L ⊚ bundleVL) v
    return id
  NEBundleP x₁ ψ₂ ψ₃ → do
    v ← lift $ elimVal ṽ
    ρ :* ṽ₂ :* ρtoṽ ← abort𝑂 $ view (nonEmpty𝐷L ⊚ bundleVL) v
    ṽ₁ ← lift $ introVal $ BaseV $ Clear $ PrinV ρ
    ṽ₃ ← lift $ introVal $ BundleV ρtoṽ
    let f₁ = bindTo x₁ ṽ₁
    f₂ ← matchVal ṽ₂ ψ₂
    f₃ ← matchVal ṽ₃ ψ₃
    return $ compose [ f₃, f₂, f₁ ]
  AscrP ψ _τ → matchVal ṽ ψ
  WildP → return id

serializeVal ∷ (STACK, Value v) ⇒ v → IM v 𝕊
serializeVal _ṽ = todoCxt

deserializeVal ∷ (STACK, Value v) ⇒ Type → 𝕊 → IM v v
deserializeVal τ s = do
  _s' :* ṽ ← parseInputType τ s
  return ṽ

muxVal ∷ (STACK, Value v) ⇒ v → v → v → IM v v
muxVal ṽ₁ ṽ₂ ṽ₃ = do
  bv₁ ← elimBase *$ elimVal ṽ₁
  v₂ ← elimVal ṽ₂
  v₃ ← elimVal ṽ₃
  v ← case (v₂, v₃) of
    (BaseV bv₂, BaseV bv₃) → do
      bv ← primBaseVal CondO $ bv₁ :& bv₂ :& bv₃ :& Nil
      return $ BaseV bv
    (ProdV ṽ₂ₗ ṽ₂ᵣ, ProdV ṽ₃ₗ ṽ₃ᵣ) → do
      ṽₗ ← muxVal ṽ₁ ṽ₂ₗ ṽ₃ₗ
      ṽᵣ ← muxVal ṽ₁ ṽ₂ᵣ ṽ₃ᵣ
      return $ ProdV ṽₗ ṽᵣ
    _ → throwIErrorCxt NotImplementedIError "oops!" $ frhs
        [ ("v₂", pretty v₂)
        , ("v₃", pretty v₃)
        ]
  introVal v

sumVal ∷ (STACK, Value v) ⇒ v → v → IM v v
sumVal ṽ₁ ṽ₂ = do
  v₁ ← elimVal ṽ₁
  v₂ ← elimVal ṽ₂
  v ← case (v₁, v₂) of
    (BaseV bv₁, BaseV bv₂) → do
      bv ← primBaseVal PlusO $ bv₁ :& bv₂ :& Nil
      return $ BaseV bv
    _ → todoCxt
  introVal v

embedBaseVal ∷ (STACK, Value v) ⇒ Prot → 𝑃 PrinVal → (BaseVal (EBV v)) → IM v (EBV v)
embedBaseVal φ ρ𝑃 = \case
  Clear cbv → embedEBV φ ρ𝑃 cbv
  bv        → elimEncrypted φ ρ𝑃 bv

embedBaseVals ∷ (STACK, Value v) ⇒ 𝐿 (BaseVal (EBV v)) → IM v (𝐿 ClearBaseVal ∨ Prot ∧ 𝑃 PrinVal ∧ 𝐿 (EBV v))
embedBaseVals bvs = do
  let meta = metaBaseVals bvs
  case meta of
    None           → Inl                ^$ mapM elimClear bvs
    Some (φ :* ρ𝑃) → Inr ∘ (φ :* ρ𝑃 :*) ^$ mapM (embedBaseVal φ ρ𝑃) bvs

primBaseVal ∷ (STACK, Value v) ⇒ Op → 𝐿 (BaseVal (EBV v)) → IM v (BaseVal (EBV v))
primBaseVal op bvs = do
  bvsₑ ← embedBaseVals bvs
  case bvsₑ of
    Inl cbvs              → Clear          ^$ evalPrimClearBaseVal op cbvs
    Inr (φ :* ρ𝑃 :* ebvs) → Encrypted φ ρ𝑃 ^$ primEBV φ ρ𝑃 op ebvs

primVal ∷ (STACK, Value v) ⇒ Op → 𝐿 v → IM v v
primVal op ṽs = do
  bvs ← mapM (elimBase *∘ elimVal) ṽs
  bv  ← primBaseVal op bvs
  introVal $ BaseV bv
