module Symphony.Interpreter where

import UVMHS
import AddToUVMHS

import Symphony.Config
import Symphony.Parser
import Symphony.Syntax

import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.ReadType
import Symphony.Interpreter.Types
import Symphony.Interpreter.Operations
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Seq
import Symphony.Interpreter.Dist
import Symphony.Interpreter.Lens
import Symphony.Interpreter.Error

import qualified Prelude as HS
import qualified System.Console.GetOpt as O
import qualified Crypto.Random as R
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Binary as B

import Foreign.ForeignPtr

-----------------------------
--- Principal Expressions ---
-----------------------------

interpPrinExp ∷ (STACK, Value v) ⇒ PrinExp → IM v PrinVal
interpPrinExp = \case
  VarPE x       → elimPrin *$ elimClear *$ elimBase *$ elimVal *$ interpVar x
  AccessPE x n₁ → do
    ρ :* n₂ ← elimPrinArr *$ elimPrinSet *$ elimClear *$ elimBase *$ elimVal *$ interpVar x
    guardErr (0 ≤ n₁ ⩓ n₁ < n₂) $
      throwIErrorCxt TypeIError "interpPrinExp: n₁ ∉ ρ[n₂]" $ frhs
      [ ("n₁", pretty n₁)
      , ("ρ", pretty ρ)
      , ("n₂", pretty n₂)
      ]
    return $ AccessPV ρ n₁

interpPrinSetExp ∷ (STACK, Value v) ⇒ PrinSetExp → IM v PrinSetVal
interpPrinSetExp = \case
  VarPSE x   → elimPrinSet *$ elimClear *$ elimBase *$ elimVal *$ interpVar x
  PowPSE ρes → PowPSV ^$ pow ^$ mapM interpPrinExp ρes
  ThisPSE    → do
    m   ← askL iCxtModeL
    ρvs ← error𝑂 (view addTopL m) $
          throwIErrorCxt TypeIError "interpPrinSetExp (ThisPSE): m ≡ ⊤" empty𝐿
    return $ PowPSV ρvs

-----------------
--- Variables ---
-----------------

interpVar ∷ (STACK, Value v) ⇒ Var → IM v v
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some v → locateVal v
    None   → throwIErrorCxt SyntaxIError "interpVar: x ∉ dom(γ)" $ frhs
             [ ("x", pretty x)
             , ("dom(γ)", pretty $ keys γ)
             ]

------------------
--- Primitives ---
------------------

interpBul ∷ (STACK, Value v) ⇒ IM v v
interpBul = introVal $ BaseV $ Clear BulV

interpBool ∷ (STACK, Value v) ⇒ 𝔹 → IM v v
interpBool b = introVal $ BaseV $ Clear $ BoolV b

interpNat ∷ (STACK, Value v) ⇒ IPrecision → ℕ → IM v v
interpNat pr n = introVal $ BaseV $ Clear $ NatV pr n

interpInt ∷ (STACK, Value v) ⇒ IPrecision → ℤ → IM v v
interpInt pr z = introVal $ BaseV $ Clear $ IntV pr z

interpFlt ∷ (STACK, Value v) ⇒ FPrecision → 𝔻 → IM v v
interpFlt pr d = introVal $ BaseV $ Clear $ FltV pr d

interpStr ∷ (STACK, Value v) ⇒ 𝕊 → IM v v
interpStr s = introVal $ BaseV $ Clear $ StrV s

interpPrin ∷ (STACK, Value v) ⇒ PrinExp → IM v v
interpPrin ρe =
  let c = interpPrinExp ρe
  in do
    ρv ← c
    introVal $ BaseV $ Clear $ PrinV ρv

interpPrinSet ∷ (STACK, Value v) ⇒ PrinSetExp → IM v v
interpPrinSet ρse =
  let c = interpPrinSetExp ρse
  in do
    ρsv ← c
    introVal $ BaseV $ Clear $ PrinSetV ρsv

interpPrim ∷ (STACK, Value v) ⇒ Op → 𝐿 Exp → IM v v
interpPrim op es =
  let cs = map interpExp es
  in do
    primVal op *$ exchange cs

---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

interpProd ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpProd eₗ eᵣ =
  let cₗ = interpExp eₗ
      cᵣ = interpExp eᵣ
  in do
    ṽₗ ← cₗ
    ṽᵣ ← cᵣ
    introVal $ ProdV ṽₗ ṽᵣ

interpL ∷ (STACK, Value v) ⇒ Exp → IM v v
interpL eₗ =
  let cₗ = interpExp eₗ
  in do
    bvₜ ← introClear $ BoolV True
    ṽₗ  ← cₗ
    ṽᵣ  ← interpDefault
    introVal $ SumV bvₜ ṽₗ ṽᵣ

interpR ∷ (STACK, Value v) ⇒ Exp → IM v v
interpR eᵣ =
  let cᵣ = interpExp eᵣ
  in do
    bvₜ ← introClear $ BoolV False
    ṽₗ  ← interpDefault
    ṽᵣ  ← cᵣ
    introVal $ SumV bvₜ ṽₗ ṽᵣ

interpNil ∷ (STACK, Value v) ⇒ IM v v
interpNil = introVal $ ListV Nil

interpCons ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpCons eₕ eₜ =
  let cₕ = interpExp eₕ
      cₜ = interpExp eₜ
  in do
    ṽ  ← cₕ
    ṽs ← elimList *$ elimVal *⋅ cₜ
    introVal $ ListV $ ṽ :& ṽs

interpIf ∷ (STACK, Value v) ⇒ Exp → Exp → Exp → IM v v
interpIf e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
    b ← elimBool *$ elimClear *$ elimBase *$ elimVal *⋅ c₁
    if b then c₂ else c₃

interpCase ∷ (STACK, Value v) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM v v
interpCase e ψes =
  let c  = interpExp e
      fs = mapOn ψes $ \ (ψ :* e') →
        let c' = interpExp e'
        in \ ṽ → do
          f ← matchVal ṽ ψ
          return $ f :* c'
  in do
    ṽ ← c
    fc𝑂 ← unFailT $ tries $ map (\ f → f ṽ) fs
    f :* cₘ ← error𝑂 fc𝑂 $
              throwIErrorCxt TypeIError "interpCase: ṽ doesn't match any of ψes" $ frhs
              [ ("ṽ", pretty ṽ)
              , ("ψes", pretty ψes)
              ]
    f cₘ

-----------------
--- Functions ---
-----------------

interpLet ∷ (STACK, Value v) ⇒ Pat → Exp → Exp → IM v v
interpLet ψ e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    ṽ₁ ← c₁
    f  ← bindVal ṽ₁ ψ
    f c₂

interpLam ∷ (STACK, Value v) ⇒ 𝑂 Var → 𝐿 Pat → Exp → IM v v
interpLam self𝑂 ψs e = do
  ψ :* ψs' ← error𝑂 (view consL ψs) $
             throwIErrorCxt TypeIError "interpLam: view consL ψs ≡ None" $ frhs
             [ ("ψs", pretty ψs)
             ]
  let e' = if ψs' ≡ Nil
           then e
           else siphon e $ LamE None ψs' e
  γ ← askL iCxtEnvL
  let c' = interpExp e'
  introVal $ CloV self𝑂 $ NoEq $ \ selfγ ṽ → do
    ψγ ← bindVal ṽ ψ
    compose [localL iCxtEnvL γ, ψγ, selfγ] c'

evalApp ∷ (STACK, Value v) ⇒ v → v → IM v v
evalApp ṽ₁ ṽ₂ = do
  self𝑂 :* f₁ ← elimClo *$ elimVal ṽ₁
  let selfγ = case self𝑂 of
                None      → id
                Some self → bindTo self ṽ₁
  f₁ selfγ ṽ₂

interpApp ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpApp e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  ṽ₁ ← c₁
  ṽ₂ ← c₂
  evalApp ṽ₁ ṽ₂

----------------------
--- Read and Write ---
----------------------

interpRead ∷ (STACK, Value v) ⇒ Type → Exp → IM v v
interpRead τ e =
  let c = interpExp e
  in do
    fn ← elimStr *$ elimClear *$ elimBase *$ elimVal *⋅ c
    ρ  ← singletonMode
    path ← inputPath ρ fn
    deserializeVal τ *$ io $ fread path

interpWrite ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpWrite e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    fn   ← elimStr *$ elimClear *$ elimBase *$ elimVal *⋅ c₂
    ρ    ← singletonMode
    path ← outputPath ρ fn
    s    ← serializeVal *⋅ c₁
    io $ fwrite path s
    interpBul

-------------
--- Trace ---
-------------

interpTrace ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpTrace e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    pptraceM *⋅ c₁
    c₂

------------------
--- References ---
------------------

interpRef ∷ (STACK, Value v) ⇒ Exp → IM v v
interpRef e =
  let c₁ = interpExp e
  in do
  ṽ ← c₁
  r ← io $ newℝMut ṽ
  introVal *$ introLoc (Inl r)

interpRefRead ∷ (STACK, Value v) ⇒ Exp → IM v v
interpRefRead e =
  let c₁ = interpExp e
  in do
  r ← elimRef *$ elimLocRead *$ elimVal *⋅ c₁
  ṽᵣ ← io $ readℝMut r
  locateVal ṽᵣ

interpRefWrite ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpRefWrite e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  r ← elimRef *$ elimLocWrite *$ elimVal *⋅ c₁
  ṽ₂ ← c₂
  io $ writeℝMut r ṽ₂
  return ṽ₂

--------------
--- Arrays ---
--------------

interpArray ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpArray e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimVal *⋅ c₁
  ṽ₂ ← c₂
  a  ← io $ vecIMut $ replicate n ṽ₂
  introVal *$ introLoc (Inr a)

interpArrayRead ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpArrayRead e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  a  ← elimArr *$ elimLocRead *$ elimVal *⋅ c₁
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimVal *⋅ c₂
  ṽᵣ ← errorIO (idx𝕍Mut (natΩ64 n) a) $
    throwIErrorCxt TypeIError "interpArrayRead: a[n] out of bounds" $ frhs
    [ ("a", pretty a)
    , ("n", pretty n)
    ]
  locateVal ṽᵣ

interpArrayWrite ∷ (STACK, Value v) ⇒ Exp → Exp → Exp → IM v v
interpArrayWrite e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
  a  ← elimArr *$ elimLocWrite *$ elimVal *⋅ c₁
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimVal *⋅ c₂
  ṽ₃ ← c₃
  errorIO (set𝕍Mut (natΩ64 n) ṽ₃ a) $
      throwIErrorCxt TypeIError "interpArrayWrite: a[n] out of bounds" $ frhs
      [ ("a", pretty a)
      , ("n", pretty n)
      ]
  return ṽ₃

interpArraySize ∷ (STACK, Value v) ⇒ Exp → IM v v
interpArraySize e = do
  a ← elimArr *$ elimLocRead *$ elimVal *$ interpExp e
  interpNat iprDefault $ nat $ length𝕍Mut a

-----------
--- Par ---
-----------

interpPar ∷ (STACK, Value v) ⇒ PrinSetExp → Exp → IM v v
interpPar ρse₁ e₂ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpExp e₂
  in do
    m  ← askL iCxtModeL
    ρ𝑃 ← elimPSV ^$ c₁
    let l = AddTop ρ𝑃
    let m' = m ⊓ l
    isInPrins ← inPrins ρ𝑃
    if m' ≢ bot ⩓ isInPrins then
      localL iCxtModeL m' c₂
    else
      return unknownVal


-----------
--- Rand --
-----------

randBaseVal ∷ (R.DRG g) ⇒ g → BaseType → ClearBaseVal ∧ g
randBaseVal g μ = case μ of
  UnitT → BulV :* g
  𝔹T    → mapFst BoolV $ frhs $ R.withRandomBytes g (HS.fromIntegral 1) (even ∘ (B.decode @ℕ8) ∘ BSL.fromStrict)
  ℕT pr → case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → mapFst ((NatV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 1) ((B.decode @ℕ8) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → mapFst ((NatV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 2) ((B.decode @ℕ16) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → mapFst ((NatV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 4) ((B.decode @ℕ32) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → mapFst ((NatV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 8) ((B.decode @ℕ64) ∘ BSL.fromStrict)
            _ → undefined -- TODO
  ℤT pr → case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → mapFst ((IntV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 1) ((B.decode @ℤ8) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → mapFst ((IntV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 2) ((B.decode @ℤ16) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → mapFst ((IntV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 4) ((B.decode @ℤ32) ∘ BSL.fromStrict)
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → mapFst ((IntV pr) ∘ HS.fromIntegral) $ frhs $ R.withRandomBytes g (HS.fromIntegral 8) ((B.decode @ℤ64) ∘ BSL.fromStrict)
            _ → undefined -- TODO
  _     → undefined -- TODO

interpRand ∷ (STACK, Value v) ⇒ PrinSetExp → BaseType → IM v v
interpRand ρse μ = do
  m  ← askL iCxtModeL
  m' ← AddTop ^$ elimPSV ^$ interpPrinSetExp ρse
  guardErr (m ≡ m') $
    throwIErrorCxt TypeIError "interpRand: m ≢ m'" $ frhs
    [ ("m", pretty m)
    , ("m'", pretty m')
    ]
  g ← getL iStateGenL
  let v :* g' = randBaseVal g μ
  putL iStateGenL g'
  introVal $ BaseV $ Clear v

-------------------------------
--- Share, Reveal, and Send ---
-------------------------------

modeCheckComm ∷ PrinVal → 𝑃 PrinVal → IM v ()
modeCheckComm ρv₁ ρvs₂ = do
  m ← askL iCxtModeL
  let nonEmpty   = not $ isEmpty ρvs₂
  let allPresent = (AddTop $ (single𝑃 ρv₁) ∪ ρvs₂) ≡ m
  guardErr nonEmpty $
    throwIErrorCxt TypeIError "modeCheckComm: ρvs₂ ≡ ø" $ frhs
    [ ("ρvs₂", pretty ρvs₂)
    ]
  guardErr allPresent $
    throwIErrorCxt TypeIError "modeCheckSync: (AddTop $ (single𝑃 ρv₁) ∪ ρvs₂) ≢ m" $ frhs
    [ ("ρv₁", pretty ρv₁)
    , ("ρvs₂", pretty ρvs₂)
    , ("m", pretty m)
    ]

interpShare ∷ (STACK, Value v) ⇒ Prot → Type → PrinExp → PrinSetExp → Exp → IM v v
interpShare φ τ ρe₁ ρse₂ e₃ =
  let c₁ = interpPrinExp ρe₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvFr  ← c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvFr ρvsTo
    shareVal φ ρvFr ρvsTo ṽ τ

interpReveal ∷ (STACK, Value v) ⇒ Prot → Type → PrinSetExp → PrinExp → Exp → IM v v
interpReveal φ τ ρse₁ ρe₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinExp ρe₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvTo  ← c₂
    ṽ     ← c₃
    modeCheckComm ρvTo ρvsFr
    revealVal φ ρvsFr ρvTo ṽ τ

interpComm ∷ (STACK, Value v) ⇒ Type → PrinExp → PrinSetExp → Exp → IM v v
interpComm τ ρe₁ ρse₂ e₃ =
  let c₁ = interpPrinExp ρe₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvFr  ← c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvFr ρvsTo
    commVal ρvFr ρvsTo ṽ τ

interpFlush ∷ (STACK, Value v) ⇒ PrinExp → IM v v
interpFlush ρe =
  let c = interpPrinExp ρe
  in do
    ρvThem ← c
    flushVal ρvThem
    interpBul

----------------------
--- MPC Operations ---
----------------------

interpMuxIf ∷ (STACK, Value v) ⇒ Exp → Exp → Exp → IM v v
interpMuxIf e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
    ṽ₁    ← c₁
    negṽ₁ ← primVal NotO $ ṽ₁ :& Nil
    ṽ₂    ← mapEnvL iCxtMPCPathConditionL (ṽ₁ :&)    c₂
    ṽ₃    ← mapEnvL iCxtMPCPathConditionL (negṽ₁ :&) c₃
    muxVal ṽ₁ ṽ₂ ṽ₃

interpMuxCase ∷ (STACK, Value v) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM v v
interpMuxCase e ψes =
  let c  = interpExp e
      fs = mapOn ψes $ \ (ψ :* e') →
        let c' = interpExp e'
        in \ ṽ → do
          f𝑂 ← unFailT $ matchVal ṽ ψ
          case f𝑂 of
            None   → return Nil
            Some f → single ^$ f c'
  in do
    ṽ ← c
    ṽs ← concat ^$ mapMOn fs $ \ f → f ṽ
    ṽₕ :* ṽsₜ ← error𝑂 (view consL ṽs) $
                throwIErrorCxt TypeIError "interpMuxCase: ṽ doesn't match any of ψes" $ frhs
                [ ("ṽ", pretty ṽ)
                , ("ψes", pretty ψes)
                ]
    mfold ṽₕ sumVal ṽsₜ

interpProc ∷ (STACK, Value v) ⇒ Exp → IM v v
interpProc e =
  let c = interpExp e
  in do
    κ :* v₀ ←
      localizeL iStateMPCContL null $
      localL iCxtMPCPathConditionL null $
      c
    mfoldrOnFrom (reverse κ) v₀ $ \ (pcᴿ :* v₁) v₂ → mfoldrOnFrom pcᴿ v₁ $ \ vᵖᶜ acc → muxVal vᵖᶜ acc v₂

interpReturn ∷ (STACK, Value v) ⇒ Exp → IM v v
interpReturn e =
  let c = interpExp e
  in do
    ṽ ← c
    pc ← askL iCxtMPCPathConditionL
    modifyL iStateMPCContL $ \ κ → (pc :* ṽ) :& κ
    interpDefault

---------------
--- Bundles ---
---------------

interpBundle ∷ (STACK, Value v) ⇒ 𝐿 (PrinExp ∧ Exp) → IM v v
interpBundle ρee𝐿 =
  let cc𝐿 = map (mapPair interpPrinExp interpExp) ρee𝐿
  in
  introVal *$ BundleV ^$ dict ^$ mapMOn (iter cc𝐿) $ \ (c₁ :* c₂) → do
    ρ ← c₁
    ṽ ← c₂
    return $ ρ ↦ ṽ

interpBundleAccess ∷ (STACK, Value v) ⇒ Exp → PrinExp → IM v v
interpBundleAccess e₁ ρe₂ =
  let c₁ = interpExp e₁
      c₂ = interpPrinExp ρe₂
  in do
    bdl ← elimBundle *$ elimVal *⋅ c₁
    ρ   ← c₂
    error𝑂 (view justL $ bdl ⋕? ρ) $
      throwIErrorCxt TypeIError "interpBundleAccess: ρ ∉ dom(bdl)" $ frhs
      [ ("ρ", pretty ρ)
      , ("dom(bdl)", pretty $ keys bdl)
      ]

interpBundleUnion ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpBundleUnion e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    bdl₁ ← elimBundle *$ elimVal *⋅ c₁
    bdl₂ ← elimBundle *$ elimVal *⋅ c₂
    introVal $ BundleV $ bdl₁ ⩌ bdl₂

------------------
--- Sequencing ---
------------------

interpSeq ∷ (STACK, Value v) ⇒ Exp → Exp → IM v v
interpSeq e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    _ ← c₁
    c₂

---------------
--- Default ---
---------------

interpDefault ∷ (STACK, Value v) ⇒ IM v v
interpDefault = introVal DefaultV

-------------------
--- Expressions ---
-------------------

--wrapInterp ∷ (STACK) ⇒ (ExpR → IM v a) → Exp → IM v a
--wrapInterp f e = localL iCxtSourceL (Some $ atag e) $ f $ extract e

interpExp ∷ (STACK, Value v) ⇒ Exp → IM v v
interpExp e = localL iCxtSourceL (Some $ atag e) $ interpExpR $ extract e

interpExpR ∷ (STACK, Value v) ⇒ ExpR → IM v v
interpExpR = \case
  -- Variables
  VarE x → interpVar x

  -- Literals
  BulE        → interpBul
  BoolE b     → interpBool b
  NatE pr n   → interpNat pr n
  IntE pr z   → interpInt pr z
  FltE pr d   → interpFlt pr d
  StrE s      → interpStr s
  PrinSetE es → interpPrinSet es
  PrimE op es → interpPrim op es

  -- Sums, Products, and Lists
  ProdE eₗ eᵣ  → interpProd eₗ eᵣ
  LE eₗ        → interpL eₗ
  RE eᵣ        → interpR eᵣ
  NilE         → interpNil
  ConsE eₕ eₜ  → interpCons eₕ eₜ
  IfE e₁ e₂ e₃ → interpIf e₁ e₂ e₃
  CaseE e ψes  → interpCase e ψes

  -- Functions
  LetE ψ e₁ e₂    → interpLet ψ e₁ e₂
  LamE self𝑂 ψs e → interpLam self𝑂 ψs e
  AppE e₁ e₂      → interpApp e₁ e₂


  -- Read and Write
  ReadE τ e    → interpRead τ e
  WriteE e₁ e₂ → interpWrite e₁ e₂

  -- Trace
  TraceE e₁ e₂ → interpTrace e₁ e₂

  -- References
  RefE e          → interpRef e
  RefReadE e      → interpRefRead e
  RefWriteE e₁ e₂ → interpRefWrite e₁ e₂

  -- Arrays
  ArrayE e₁ e₂                                → interpArray e₁ e₂
  ArrayReadE e₁ e₂                            → interpArrayRead e₁ e₂
  ArrayWriteE (extract → ArrayReadE e₁ e₂) e₃ → interpArrayWrite e₁ e₂ e₃
  ArraySizeE e                                → interpArraySize e

  -- Par
  ParE ρse₁ e₂ → interpPar ρse₁ e₂

  -- Rand
  RandE ρse μ → interpRand ρse μ

  -- Share, Reveal, and Send
  ShareE φ τ ρe₁ ρse₂ e₃  → interpShare φ τ ρe₁ ρse₂ e₃
  RevealE φ τ ρse₁ ρe₂ e₃ → interpReveal φ τ ρse₁ ρe₂ e₃
  SendE τ ρe₁ ρse₂ e₃     → interpComm τ ρe₁ ρse₂ e₃
  FlushE ρe               → interpFlush ρe

  -- MPC Operations
  MuxIfE e₁ e₂ e₃ → interpMuxIf e₁ e₂ e₃
  MuxCaseE e ψes  → interpMuxCase e ψes
  ProcE e         → interpProc e
  ReturnE e       → interpReturn e

  -- Bundles
  BundleE ρees         → interpBundle ρees
  BundleAccessE e₁ ρe₂ → interpBundleAccess e₁ ρe₂
  BundleUnionE e₁ e₂   → interpBundleUnion e₁ e₂

  -- Sequencing
  SeqE e₁ e₂ → interpSeq e₁ e₂

  -- Default
  DefaultE → interpDefault

  -- TODO
  _ → todoCxt

---------------
-- TOP LEVEL --
---------------

asTLM ∷ (Value v) ⇒ IM v a → ITLM v a
asTLM xM = mkITLM $ \ θ ωtl →
  let γ       = itlStateEnv ωtl
      ω       = itlStateExp ωtl
      ds      = itlStatePrinScope ωtl
      ξ       = compose
                [ update iCxtParamsL θ
                , update iCxtEnvL γ
                , update iCxtPrinScopeL ds
                ]
                ξ₀
  in do
    rox ← runIM ξ ω xM
    return $ case rox of
      Inl r → Inl r
      Inr (ω' :* o :* x) →
        let ωtl' = update itlStateExpL ω' ωtl in
          Inr $ ωtl' :* o :* x

interpTL ∷ (Value v) ⇒ TL → ITLM v ()
interpTL tl = case extract tl of
  DeclTL _ _ _ → skip
  DefnTL b x ψs e →
    let e' =
          if b
          then buildUnfixedLambda (atag tl) x ψs e
          else buildLambda (atag tl) x ψs e
        c  = interpExp e'
    in do
      v ← asTLM c
      modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL ρds → do
    γρs :* ρScope ← split ^$ mapMOn ρds $ \case
      SinglePD ρ → do
        let ρv = SinglePV ρ
        ṽ ← asTLM $ introVal $ BaseV $ Clear $ PrinV ρv
        return $ (var ρ ↦ ṽ) :* single ρv
      ArrayPD ρ n → do
        let ρsv = ArrPSV ρ n
        ṽ ← asTLM $ introVal $ BaseV $ Clear $ PrinSetV ρsv
        return $ (var ρ ↦ ṽ) :* elimPSV ρsv
    modifyL itlStateEnvL ((dict γρs) ⩌)
    modifyL itlStatePrinScopeL ((concat ρScope) ∪)
  ImportTL path → do
    s ← io $ fread path
    let ts = tokens s
    ls ← io $ tokenizeIO lexer path ts
    tls ← io $ parseIO cpTLs path ls
    interpTLs tls

interpTLs ∷ (Value v) ⇒ 𝐿 TL → ITLM v ()
interpTLs = eachWith interpTL

-- ==== --
-- MAIN --
-- ==== --

-------------
-- Options --
-------------

data Options = Options
  { optVersion ∷ 𝔹
  , optHelp ∷ 𝔹
  , optRandomSeed ∷ 𝑂 ℕ
  , optParty ∷ 𝑂 Prin
  , optTestsPath ∷ 𝕊
  , optLibPath ∷ 𝕊
  }
  deriving (Eq,Ord,Show)
makeLenses ''Options

options₀ ∷ IO Options
options₀ = do
  localTestsExists ← pexists "tests"
  testsPath ←
    if localTestsExists
    then return "tests"
    else datapath "tests"
  libPathExists ← pexists "lib"
  libPath ←
    if libPathExists
    then return "lib"
    else datapath "lib"
  return $ Options
    { optVersion = False
    , optHelp = False
    , optRandomSeed = None
    , optParty = None
    , optTestsPath = testsPath
    , optLibPath = libPath
    }

usageInfoTop ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTop = frhs
  [ O.Option ['v'] [chars "version"]
             (O.NoArg $ update optVersionL True)
           $ chars "print version"
  , O.Option ['h'] [chars "help"]
             (O.NoArg $ update optHelpL True)
           $ chars "show help"
  ]

usageInfoRun ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoRun = frhs
  [ O.Option ['P'] [chars "party"]
             (O.ReqArg (\ s → update optPartyL $ Some $ string s) $ chars "PRIN")
           $ chars "set current party"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoExample ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoExample = frhs
  [ O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoTest ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTest = frhs
  [ O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

readPrinVal ∷ 𝕊 → 𝑂 PrinVal
readPrinVal s = case list $ splitOn𝕊 "." s of
  ρ :& Nil      → Some $ SinglePV ρ
  ρ :& n :& Nil → Some $ AccessPV ρ (read𝕊 n)
  _             → None

initializeEnv ∷ Options → IParams
initializeEnv os = flip compose θ₀
  [ update iParamsMeL $ mjoin $ readPrinVal ^$ optParty os ]

parseOptionsSymphony ∷ IO (Options ∧ 𝐿 𝕊)
parseOptionsSymphony = do
  as ← iargs
  let fs :* nos :* ems = parseOptions (usageInfoTop ⧺ usageInfoRun) as
  eachOn ems out
  os ← compose fs ^$ options₀
  when (optVersion os) $ do
    out $ "symphony version " ⧺ symphony_VERSION
  when (optVersion os ⩓ optHelp os) $ do
    out ""
  when (optHelp os) $ do
    out "Usage: symphony [<command>] [<arguments>] [<target>]"
    out ""
    out $ optUsageInfo "symphony [arguments]" usageInfoTop
    out $ optUsageInfo "symphony run [arguments] <file>" usageInfoRun
    out $ optUsageInfo "symphony example [arguments] <name>"  usageInfoExample
    out $ optUsageInfo "symphony test [arguments]" usageInfoTest
  return $ os :* nos

parseFile ∷ 𝕊 → 𝕊 → IO (𝐿 TL)
parseFile name path = do
  s ← fread path
  let ts = tokens s
  ls ← tokenizeIO lexer name ts
  parseIO cpTLs name ls

interpretFile ∷ (Value v) ⇒ IParams → ITLState v → 𝕊 → 𝕊 → IO (ITLState v)
interpretFile θ ωtl name path = do
  tls ← parseFile name path
  ωtl' :* _ :* () ← din (pdirectory path) $ runITLMIO θ ωtl name $ eachWith interpTL tls
  return ωtl'

interpretFileMain ∷ (Value v) ⇒ IParams → ITLState v → 𝕊 → 𝕊 → IO v
interpretFileMain θ ωtl name path = do
  ωtl' ← interpretFile θ ωtl name path
  let main = itlStateEnv ωtl' ⋕! var "main"
  ωtl'' :* _ :* v ← runITLMIO θ ωtl' name $ asTLM $ do
    bul ← introVal $ BaseV $ Clear BulV
    evalApp main bul
  eachWith finalizeForeignPtr $ values (iStateSessionsYao (itlStateExp ωtl''))
  return v

interpMain ∷ (Value v) ⇒ ITLM v v
interpMain = asTLM $ do
  main ← interpVar $ var "main"
  bul  ← introVal $ BaseV $ Clear BulV
  evalApp main bul

interpretSeq ∷ IParams → ITLState SeqVal → 𝕊 → 𝕊 → IO (ITLState SeqVal)
interpretSeq = interpretFile

interpretSeqMain ∷ IParams → ITLState SeqVal → 𝕊 → 𝕊 → IO SeqVal
interpretSeqMain = interpretFileMain

interpretDist ∷ IParams → ITLState DistVal → 𝕊 → 𝕊 → IO (ITLState DistVal)
interpretDist = interpretFile

interpretDistMain ∷ IParams → ITLState DistVal → 𝕊 → 𝕊 → IO DistVal
interpretDistMain = interpretFileMain
