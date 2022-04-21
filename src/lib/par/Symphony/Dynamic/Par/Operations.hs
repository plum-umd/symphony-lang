module Symphony.Dynamic.Par.Operations where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.ReadType
import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Dist
import Symphony.Dynamic.Par.Primitives
import Symphony.Dynamic.Par.Error

-----------------
--- Utilities ---
-----------------

bindTo ∷ (STACK) ⇒ Var → Val → IM Val a → IM Val a
bindTo x ṽ = mapEnvL iCxtEnvL ((x ↦ ṽ) ⩌)

bindVal ∷ (STACK) ⇒ Val → Pat → IM Val (IM Val Val → IM Val Val)
bindVal ṽ ψ = do
  f𝑂 ← unFailT $ matchVal ṽ ψ
  error𝑂 f𝑂 $
    throwIErrorCxt TypeIError "bindVal: ṽ doesn't match ψ" $ frhs
    [ ("ṽ", pretty ṽ)
    , ("ψ", pretty ψ)
    ]

singletonMode ∷ (STACK) ⇒ IM Val PrinVal
singletonMode = do
  m ← askL iCxtModeL
  error𝑂 (view (one𝑃L ⊚ addTopL) m) $
    throwIErrorCxt TypeIError "singletonMode: view (one𝑃L ⊚ addTopL) m" $ frhs
    [ ("m", pretty m)
    ]

defaultClearValR ∷ (STACK) ⇒ Type → ValR
defaultClearValR = \case
  BaseT bτ → BaseV $ ClearV $ defaultClearBaseVal bτ
  _        → undefined --TODO

------------------------
--- ValR Convenience ---
------------------------

introLoc ∷ (STACK) ⇒ (ℝMut Val ∨ 𝕍Mut Val) → IM Val ValR
introLoc ℓ = do
  m ← askL iCxtModeL
  return $ LocV m ℓ

elimBase ∷ (STACK) ⇒ ValR → IM Val BaseVal
elimBase v = error𝑂 (view baseVL v) $
             throwIErrorCxt TypeIError "elimBase: view baseVL v ≡ None" $ frhs
             [ ("v", pretty v)
             ]

elimList ∷ (STACK) ⇒ ValR → IM Val (𝐿 Val)
elimList v = error𝑂 (view listVL v) $
             throwIErrorCxt TypeIError "elimList: view listVL v ≡ None" $ frhs
             [ ("v", pretty v)
             ]

elimClo ∷ (STACK) ⇒ ValR → IM Val (𝑂 Var ∧ ((IM Val Val → IM Val Val) → Val → IM Val Val))
elimClo v = do
  self𝑂 :* fne ← error𝑂 (view cloVL v) $
                 throwIErrorCxt TypeIError "elimClo: view cloVL v ≡ None" $ frhs
                 [ ("v", pretty v)
                 ]
  return $ self𝑂 :* unNoEq fne

elimLocRead ∷ (STACK) ⇒ ValR → IM Val (ℝMut Val ∨ 𝕍Mut Val)
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

elimLocWrite ∷ (STACK) ⇒ ValR → IM Val (ℝMut Val ∨ 𝕍Mut Val)
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

elimRef ∷ (STACK) ⇒ ℝMut Val ∨ 𝕍Mut Val → IM Val (ℝMut Val)
elimRef 𝓁 = case 𝓁 of
  Inl r  → return r
  Inr _a → throwIErrorCxt TypeIError "elimRef: 𝓁 ≢ ref _" $ frhs
             [ ("𝓁", pretty 𝓁)
             ]

elimArr ∷ (STACK) ⇒ ℝMut Val ∨ 𝕍Mut Val → IM Val (𝕍Mut Val)
elimArr 𝓁 = case 𝓁 of
  Inl _r → throwIErrorCxt TypeIError "elimArr: 𝓁 ≢ arr _" $ frhs
             [ ("𝓁", pretty 𝓁)
             ]
  Inr a → return a

elimBundle ∷ (STACK) ⇒ ValR → IM Val (PrinVal ⇰ Val)
elimBundle v = error𝑂 (view bundleVL v) $
               throwIErrorCxt TypeIError "elimBundle: view bundleVL v ≡ None" $ frhs
               [ ("v", pretty v)
               ]

----------------------------
--- Operations on Values ---
----------------------------

matchLClear ∷ (STACK) ⇒ BaseVal → Val → Pat → FailT (IM Val) (IM Val Val → IM Val Val)
matchLClear bvₜ ṽₗ ψₗ = do
  cbvₜ ← abort𝑂 $ view clearVL bvₜ
  bₜ   ← lift $ elimBool cbvₜ
  if bₜ then matchVal ṽₗ ψₗ else abort

matchLEnc ∷ (STACK) ⇒ BaseVal → Val → Pat → FailT (IM Val) (IM Val Val → IM Val Val)
matchLEnc bvₜ ṽₗ ψₗ = do
  ṽₜ ← lift $ return $ KnownV $ BaseV bvₜ
  fₗ ← matchVal ṽₗ ψₗ
  return $ \ xM → do
    ṽₗᵒ ← mapEnvL iCxtMPCPathConditionL (ṽₜ :&) $ fₗ xM
    ṽᵣᵒ ← return $ KnownV $ DefaultV
    muxVal ṽₜ ṽₗᵒ ṽᵣᵒ

matchRClear ∷ (STACK) ⇒ BaseVal → Val → Pat → FailT (IM Val) (IM Val Val → IM Val Val)
matchRClear bvₜ ṽᵣ ψᵣ = do
  cbvₜ ← abort𝑂 $ view clearVL bvₜ
  bₜ   ← lift $ elimBool cbvₜ
  if not bₜ then matchVal ṽᵣ ψᵣ else abort

matchREnc ∷ (STACK) ⇒ BaseVal → Val → Pat → FailT (IM Val) (IM Val Val → IM Val Val)
matchREnc bvₜ ṽᵣ ψᵣ = do
  ṽₜ ← lift $ return $ KnownV $ BaseV bvₜ
  negṽₜ ← lift $ primVal NotO $ ṽₜ :& Nil
  fᵣ ← matchVal ṽᵣ ψᵣ
  return $ \ xM → do
    ṽₗᵒ ← return $ KnownV $ DefaultV
    ṽᵣᵒ ← mapEnvL iCxtMPCPathConditionL (negṽₜ :&) $ fᵣ xM
    muxVal ṽₜ ṽₗᵒ ṽᵣᵒ

matchVal ∷ (STACK) ⇒ Val → Pat → FailT (IM Val) (IM Val Val → IM Val Val)
matchVal ṽ = \case
  VarP x → return $ bindTo x ṽ
  BulP → do
    v ← lift $ elimKnown ṽ
    abort𝑂 $ view (bulCVL ⊚ clearVL ⊚ baseVL) v
    return id
  EPrinSetP → do
    v ← lift $ elimKnown ṽ
    ρsv ← abort𝑂 $ view (prinSetCVL ⊚ clearVL ⊚ baseVL) v
    let ρ𝑃 = elimPSV ρsv
    abort𝑂 $ view empty𝑃L ρ𝑃
    return id
  NEPrinSetP x₁ ψ₂ → do
    v ← lift $ elimKnown ṽ
    ρsv ← abort𝑂 $ view (prinSetCVL ⊚ clearVL ⊚ baseVL) v
    let ρ𝑃 = elimPSV ρsv
    ρ :* ρs ← abort𝑂 $ view nonEmpty𝑃L ρ𝑃
    ṽ₁ ← lift $ return $ KnownV $ BaseV $ ClearV $ PrinCV ρ
    ṽ₂ ← lift $ return $ KnownV $ BaseV $ ClearV $ PrinSetCV $ PowPSV ρs
    let f₁ = bindTo x₁ ṽ₁
    f₂ ← matchVal ṽ₂ ψ₂
    return $ compose [ f₂, f₁ ]
  ProdP ψₗ ψᵣ → do
    v ← lift $ elimKnown ṽ
    ṽₗ :* ṽᵣ ← abort𝑂 $ view prodVL v
    fₗ ← matchVal ṽₗ ψₗ
    fᵣ ← matchVal ṽᵣ ψᵣ
    return $ compose [ fᵣ, fₗ ]
  LP ψₗ → do
    v ← lift $ elimKnown ṽ
    bvₜ :* ṽₗ :* _ṽᵣ ← abort𝑂 $ view sumVL v
    tries [ matchLClear bvₜ ṽₗ ψₗ , matchLEnc bvₜ ṽₗ ψₗ ]
  RP ψᵣ → do
    v ← lift $ elimKnown ṽ
    bvₜ :* _ṽₗ :* ṽᵣ ← abort𝑂 $ view sumVL v
    tries [ matchRClear bvₜ ṽᵣ ψᵣ , matchREnc bvₜ ṽᵣ ψᵣ ]
  NilP → do
    v ← lift $ elimKnown ṽ
    abort𝑂 $ view (nilL ⊚ listVL) v
    return id
  ConsP ψ₁ ψ₂ → do
    v ← lift $ elimKnown ṽ
    ṽ₁ :* ṽs ← abort𝑂 $ view (consL ⊚ listVL) v
    ṽ₂ ← lift $ return $ KnownV $ ListV ṽs
    f₁ ← matchVal ṽ₁ ψ₁
    f₂ ← matchVal ṽ₂ ψ₂
    return $ compose [ f₂, f₁ ]
  EBundleP → do
    v ← lift $ elimKnown ṽ
    abort𝑂 $ view (empty𝐷L ⊚ bundleVL) v
    return id
  NEBundleP x₁ ψ₂ ψ₃ → do
    v ← lift $ elimKnown ṽ
    ρ :* ṽ₂ :* ρtoṽ ← abort𝑂 $ view (nonEmpty𝐷L ⊚ bundleVL) v
    ṽ₁ ← lift $ return $ KnownV $ BaseV $ ClearV $ PrinCV ρ
    ṽ₃ ← lift $ return $ KnownV $ BundleV ρtoṽ
    let f₁ = bindTo x₁ ṽ₁
    f₂ ← matchVal ṽ₂ ψ₂
    f₃ ← matchVal ṽ₃ ψ₃
    return $ compose [ f₃, f₂, f₁ ]
  AscrP ψ _τ → matchVal ṽ ψ
  WildP → return id

serializeVal ∷ (STACK) ⇒ Val → IM Val 𝕊
serializeVal _ṽ = todoCxt

deserializeVal ∷ (STACK) ⇒ Type → 𝕊 → IM Val Val
deserializeVal τ s = do
  _s' :* ṽ ← parseInputType τ s
  return ṽ

muxVal ∷ (STACK) ⇒ Val → Val → Val → IM Val Val
muxVal ṽ₁ ṽ₂ ṽ₃ = do
  bv₁ ← elimBase *$ elimKnown ṽ₁
  v₂ ← elimKnown ṽ₂
  v₃ ← elimKnown ṽ₃
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
  return $ KnownV v

sumVal ∷ (STACK) ⇒ Val → Val → IM Val Val
sumVal ṽ₁ ṽ₂ = do
  v₁ ← elimKnown ṽ₁
  v₂ ← elimKnown ṽ₂
  v ← case (v₁, v₂) of
    (BaseV bv₁, BaseV bv₂) → do
      bv ← primBaseVal PlusO $ bv₁ :& bv₂ :& Nil
      return $ BaseV bv
    _ → todoCxt
  return $ KnownV v

embedBaseVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → BaseVal → IM Val EncBaseVal
embedBaseVal φ ρ𝑃 = \case
  ClearV cbv → embedEBVDist φ ρ𝑃 cbv
  bv         → elimEnc ρ𝑃 bv

embedBaseVals ∷ (STACK) ⇒ 𝐿 BaseVal → IM Val (𝐿 ClearBaseVal ∨ Prot ∧ 𝑃 PrinVal ∧ 𝐿 EncBaseVal)
embedBaseVals bvs = do
  let meta = metaBaseVals bvs
  case meta of
    None           → Inl                ^$ mapM elimClear bvs
    Some (ρ𝑃 :* φ) → Inr ∘ (φ :* ρ𝑃 :*) ^$ mapM (embedBaseVal φ ρ𝑃) bvs

primBaseVal ∷ (STACK) ⇒ Op → 𝐿 BaseVal → IM Val BaseVal
primBaseVal op bvs = do
  bvsₑ ← embedBaseVals bvs
  case bvsₑ of
    Inl cbvs              → ClearV  ^$ evalPrimClearBaseVal op cbvs
    Inr (φ :* ρ𝑃 :* ebvs) → EncV ρ𝑃 ^$ primEBVDist φ ρ𝑃 op ebvs

primVal ∷ (STACK) ⇒ Op → 𝐿 Val → IM Val Val
primVal op ṽs = do
  bvs ← mapM (elimBase *∘ elimKnown) ṽs
  bv  ← primBaseVal op bvs
  return $ KnownV $ BaseV bv
