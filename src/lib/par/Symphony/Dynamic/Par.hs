module Symphony.Dynamic.Par where

import Symphony.Prelude

import Symphony.Config
import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Par.ReadType
import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Operations
import Symphony.Dynamic.Par.Dist
import Symphony.Dynamic.Par.Error

import qualified Prelude as HS
import qualified System.Console.GetOpt as O
import qualified Crypto.Random as R
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Binary as B

import Foreign.ForeignPtr

-----------------------------
--- Principal Expressions ---
-----------------------------

interpPrinExp ∷ (STACK) ⇒ PrinExp → IM Val PrinVal
interpPrinExp = \case
  VarPE x       → elimPrin *$ elimClear *$ elimBase *$ elimKnown *$ interpVar x
  AccessPE x n₁ → do
    ρ :* n₂ ← elimPrinArr *$ elimPrinSet *$ elimClear *$ elimBase *$ elimKnown *$ interpVar x
    guardErr (0 ≤ n₁ ⩓ n₁ < n₂) $
      throwIErrorCxt TypeIError "interpPrinExp: n₁ ∉ ρ[n₂]" $ frhs
      [ ("n₁", pretty n₁)
      , ("ρ", pretty ρ)
      , ("n₂", pretty n₂)
      ]
    return $ AccessPV ρ n₁

interpPrinSetExp ∷ (STACK) ⇒ PrinSetExp → IM Val PrinSetVal
interpPrinSetExp = \case
  VarPSE x   → elimPrinSet *$ elimClear *$ elimBase *$ elimKnown *$ interpVar x
  PowPSE ρes → PowPSV ^$ pow ^$ mapM interpPrinExp ρes
  ThisPSE    → do
    m   ← askL iCxtModeL
    ρvs ← error𝑂 (view addTopL m) $
          throwIErrorCxt TypeIError "interpPrinSetExp (ThisPSE): m ≡ ⊤" empty𝐿
    return $ PowPSV ρvs

-----------------
--- Variables ---
-----------------

interpVar ∷ (STACK) ⇒ Var → IM Val Val
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some v → return v
    None   → throwIErrorCxt SyntaxIError "interpVar: x ∉ dom(γ)" $ frhs
             [ ("x", pretty x)
             , ("dom(γ)", pretty $ keys γ)
             ]

------------------
--- Primitives ---
------------------

interpBul ∷ (STACK) ⇒ IM Val Val
interpBul = return $ KnownV $ BaseV $ ClearV BulV

interpBool ∷ (STACK) ⇒ 𝔹 → IM Val Val
interpBool b = return $ KnownV $ BaseV $ ClearV $ BoolV b

interpNat ∷ (STACK) ⇒ IPrecision → ℕ → IM Val Val
interpNat pr n = return $ KnownV $ BaseV $ ClearV $ NatV pr n

interpInt ∷ (STACK) ⇒ IPrecision → ℤ → IM Val Val
interpInt pr z = return $ KnownV $ BaseV $ ClearV $ IntV pr z

interpFlt ∷ (STACK) ⇒ FPrecision → 𝔻 → IM Val Val
interpFlt pr d = return $ KnownV $ BaseV $ ClearV $ FltV pr d

interpStr ∷ (STACK) ⇒ 𝕊 → IM Val Val
interpStr s = return $ KnownV $ BaseV $ ClearV $ StrV s

interpPrin ∷ (STACK) ⇒ PrinExp → IM Val Val
interpPrin ρe =
  let c = interpPrinExp ρe
  in do
    ρv ← c
    return $ KnownV $ BaseV $ ClearV $ PrinV ρv

interpPrinSet ∷ (STACK) ⇒ PrinSetExp → IM Val Val
interpPrinSet ρse =
  let c = interpPrinSetExp ρse
  in do
    ρsv ← c
    return $ KnownV $ BaseV $ ClearV $ PrinSetV ρsv

interpPrim ∷ (STACK) ⇒ Op → 𝐿 Exp → IM Val Val
interpPrim op es =
  let cs = map interpExp es
  in do
    primVal op *$ exchange cs

---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

interpProd ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpProd eₗ eᵣ =
  let cₗ = interpExp eₗ
      cᵣ = interpExp eᵣ
  in do
    ṽₗ ← cₗ
    ṽᵣ ← cᵣ
    return $ KnownV $ ProdV ṽₗ ṽᵣ

interpL ∷ (STACK) ⇒ Exp → IM Val Val
interpL eₗ =
  let cₗ = interpExp eₗ
  in do
    bvₜ ← return $ ClearV $ BoolV True
    ṽₗ  ← cₗ
    ṽᵣ  ← interpDefault
    return $ KnownV $ SumV bvₜ ṽₗ ṽᵣ

interpR ∷ (STACK) ⇒ Exp → IM Val Val
interpR eᵣ =
  let cᵣ = interpExp eᵣ
  in do
    bvₜ ← return $ ClearV $ BoolV False
    ṽₗ  ← interpDefault
    ṽᵣ  ← cᵣ
    return $ KnownV $ SumV bvₜ ṽₗ ṽᵣ

interpNil ∷ (STACK) ⇒ IM Val Val
interpNil = return $ KnownV $ ListV Nil

interpCons ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpCons eₕ eₜ =
  let cₕ = interpExp eₕ
      cₜ = interpExp eₜ
  in do
    ṽ  ← cₕ
    ṽs ← elimList *$ elimKnown *⋅ cₜ
    return $ KnownV $ ListV $ ṽ :& ṽs

interpIf ∷ (STACK) ⇒ Exp → Exp → Exp → IM Val Val
interpIf e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
    b ← elimBool *$ elimClear *$ elimBase *$ elimKnown *⋅ c₁
    if b then c₂ else c₃

interpCase ∷ (STACK) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM Val Val
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

interpLet ∷ (STACK) ⇒ Pat → Exp → Exp → IM Val Val
interpLet ψ e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    ṽ₁ ← c₁
    f  ← bindVal ṽ₁ ψ
    f c₂

interpLam ∷ (STACK) ⇒ 𝑂 Var → 𝐿 Pat → Exp → IM Val Val
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
  return $ KnownV $ CloV self𝑂 $ NoEq $ \ selfγ ṽ → do
    ψγ ← bindVal ṽ ψ
    compose [localL iCxtEnvL γ, ψγ, selfγ] c'

evalApp ∷ (STACK) ⇒ Val → Val → IM Val Val
evalApp ṽ₁ ṽ₂ = do
  self𝑂 :* f₁ ← elimClo *$ elimKnown ṽ₁
  let selfγ = case self𝑂 of
                None      → id
                Some self → bindTo self ṽ₁
  f₁ selfγ ṽ₂

interpApp ∷ (STACK) ⇒ Exp → Exp → IM Val Val
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

interpRead ∷ (STACK) ⇒ Type → Exp → IM Val Val
interpRead τ e =
  let c = interpExp e
  in do
    fn ← elimStr *$ elimClear *$ elimBase *$ elimKnown *⋅ c
    ρ  ← singletonMode
    path ← inputPath ρ fn
    deserializeVal τ *$ io $ fread path

interpWrite ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpWrite e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    fn   ← elimStr *$ elimClear *$ elimBase *$ elimKnown *⋅ c₂
    ρ    ← singletonMode
    path ← outputPath ρ fn
    s    ← serializeVal *⋅ c₁
    io $ fwrite path s
    interpBul

-------------
--- Trace ---
-------------

interpTrace ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpTrace e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    pptraceM *⋅ c₁
    c₂

------------------
--- References ---
------------------

interpRef ∷ (STACK) ⇒ Exp → IM Val Val
interpRef e =
  let c₁ = interpExp e
  in do
  ṽ ← c₁
  r ← io $ newℝMut ṽ
  KnownV ^$ introLoc (Inl r)

interpRefRead ∷ (STACK) ⇒ Exp → IM Val Val
interpRefRead e =
  let c₁ = interpExp e
  in do
  r ← elimRef *$ elimLocRead *$ elimKnown *⋅ c₁
  ṽᵣ ← io $ readℝMut r
  return ṽᵣ

interpRefWrite ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpRefWrite e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  r ← elimRef *$ elimLocWrite *$ elimKnown *⋅ c₁
  ṽ₂ ← c₂
  io $ writeℝMut r ṽ₂
  return ṽ₂

--------------
--- Arrays ---
--------------

interpArray ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpArray e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimKnown *⋅ c₁
  ṽ₂ ← c₂
  a  ← io $ vecIMut $ replicate n ṽ₂
  KnownV ^$ introLoc (Inr a)

interpArrayRead ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpArrayRead e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  a  ← elimArr *$ elimLocRead *$ elimKnown *⋅ c₁
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimKnown *⋅ c₂
  ṽᵣ ← errorIO (idx𝕍Mut (natΩ64 n) a) $
    throwIErrorCxt TypeIError "interpArrayRead: a[n] out of bounds" $ frhs
    [ ("a", pretty a)
    , ("n", pretty n)
    ]
  return ṽᵣ

interpArrayWrite ∷ (STACK) ⇒ Exp → Exp → Exp → IM Val Val
interpArrayWrite e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
  a  ← elimArr *$ elimLocWrite *$ elimKnown *⋅ c₁
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimKnown *⋅ c₂
  ṽ₃ ← c₃
  errorIO (set𝕍Mut (natΩ64 n) ṽ₃ a) $
      throwIErrorCxt TypeIError "interpArrayWrite: a[n] out of bounds" $ frhs
      [ ("a", pretty a)
      , ("n", pretty n)
      ]
  return ṽ₃

interpArraySize ∷ (STACK) ⇒ Exp → IM Val Val
interpArraySize e = do
  a ← elimArr *$ elimLocRead *$ elimKnown *$ interpExp e
  interpNat iprDefault $ nat $ length𝕍Mut a

-----------
--- Par ---
-----------

interpPar ∷ (STACK) ⇒ PrinSetExp → Exp → IM Val Val
interpPar ρse₁ e₂ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpExp e₂
  in do
    m  ← askL iCxtModeL
    ρ𝑃 ← elimPSV ^$ c₁
    let l = AddTop ρ𝑃
    let m' = m ⊓ l
    isInPrins ← inPrinsDist ρ𝑃
    if m' ≢ bot ⩓ isInPrins then
      localL iCxtModeL m' c₂
    else
      return UnknownV


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

interpRand ∷ (STACK) ⇒ PrinSetExp → BaseType → IM Val Val
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
  return $ KnownV $ BaseV $ ClearV v

-------------------------------
--- Share, Reveal, and Send ---
-------------------------------

modeCheckComm ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM Val ()
modeCheckComm ρvs₁ ρvs₂ = do
  m ← askL iCxtModeL
  let nonEmpty   = not (isEmpty ρvs₁) ⩓ not (isEmpty ρvs₂)
  let allPresent = (AddTop $ ρvs₁ ∪ ρvs₂) ≡ m
  guardErr nonEmpty $
    throwIErrorCxt TypeIError "modeCheckComm: ρvs₁ ≡ ø ∨ ρvs₂ ≡ ø" $ frhs
    [ ("ρvs₁", pretty ρvs₁)
    , ("ρvs₂", pretty ρvs₂)
    ]
  guardErr allPresent $
    throwIErrorCxt TypeIError "modeCheckComm: (AddTop $ ρvs₁ ∪ ρvs₂) ≢ m" $ frhs
    [ ("ρvs₁", pretty ρvs₁)
    , ("ρvs₂", pretty ρvs₂)
    , ("m", pretty m)
    ]

interpShare ∷ (STACK) ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → IM Val Val
interpShare φ τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsFr ρvsTo
    shareVal φ ρvsFr ρvsTo ṽ τ

interpReveal ∷ (STACK) ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → IM Val Val
interpReveal φ τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsFr ρvsTo
    revealVal φ ρvsFr ρvsTo ṽ τ

interpComm ∷ (STACK) ⇒ Type → PrinSetExp → PrinSetExp → Exp → IM Val Val
interpComm τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsFr ρvsTo
    commVal ρvsFr ρvsTo ṽ τ

----------------------
--- MPC Operations ---
----------------------

interpMuxIf ∷ (STACK) ⇒ Exp → Exp → Exp → IM Val Val
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

interpMuxCase ∷ (STACK) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM Val Val
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

interpProc ∷ (STACK) ⇒ Exp → IM Val Val
interpProc e =
  let c = interpExp e
  in do
    κ :* v₀ ←
      localizeL iStateMPCContL null $
      localL iCxtMPCPathConditionL null $
      c
    mfoldrOnFrom (reverse κ) v₀ $ \ (pcᴿ :* v₁) v₂ → mfoldrOnFrom pcᴿ v₁ $ \ vᵖᶜ acc → muxVal vᵖᶜ acc v₂

interpReturn ∷ (STACK) ⇒ Exp → IM Val Val
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

interpBundle ∷ (STACK) ⇒ 𝐿 (PrinExp ∧ Exp) → IM Val Val
interpBundle ρee𝐿 =
  let cc𝐿 = map (mapPair interpPrinExp interpExp) ρee𝐿
  in
  KnownV ^$ BundleV ^$ dict ^$ mapMOn (iter cc𝐿) $ \ (c₁ :* c₂) → do
    ρ ← c₁
    ṽ ← c₂
    return $ ρ ↦ ṽ

interpBundleAccess ∷ (STACK) ⇒ Exp → PrinExp → IM Val Val
interpBundleAccess e₁ ρe₂ =
  let c₁ = interpExp e₁
      c₂ = interpPrinExp ρe₂
  in do
    bdl ← elimBundle *$ elimKnown *⋅ c₁
    ρ   ← c₂
    error𝑂 (view justL $ bdl ⋕? ρ) $
      throwIErrorCxt TypeIError "interpBundleAccess: ρ ∉ dom(bdl)" $ frhs
      [ ("ρ", pretty ρ)
      , ("dom(bdl)", pretty $ keys bdl)
      ]

interpBundleUnion ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpBundleUnion e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    bdl₁ ← elimBundle *$ elimKnown *⋅ c₁
    bdl₂ ← elimBundle *$ elimKnown *⋅ c₂
    return $ KnownV $ BundleV $ bdl₁ ⩌ bdl₂

------------------
--- Sequencing ---
------------------

interpSeq ∷ (STACK) ⇒ Exp → Exp → IM Val Val
interpSeq e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    _ ← c₁
    c₂

---------------
--- Default ---
---------------

interpDefault ∷ (STACK) ⇒ IM Val Val
interpDefault = return $ KnownV DefaultV

-------------------
--- Expressions ---
-------------------

--wrapInterp ∷ (STACK) ⇒ (ExpR → IM Val a) → Exp → IM Val a
--wrapInterp f e = localL iCxtSourceL (Some $ atag e) $ f $ extract e

interpExp ∷ (STACK) ⇒ Exp → IM Val Val
interpExp e = localL iCxtSourceL (Some $ atag e) $ interpExpR $ extract e

interpExpR ∷ (STACK) ⇒ ExpR → IM Val Val
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
  ShareE φ τ ρes₁ ρse₂ e₃  → interpShare φ τ ρes₁ ρse₂ e₃
  RevealE φ τ ρse₁ ρes₂ e₃ → interpReveal φ τ ρse₁ ρes₂ e₃
  SendE τ ρes₁ ρse₂ e₃     → interpComm τ ρes₁ ρse₂ e₃

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

asTLM ∷ IM Val a → ITLM Val a
asTLM xM = mkITLM $ \ θ ωtl →
  let γ       = itlStateEnv ωtl
      ω       = itlStateExp ωtl
      ds      = itlStatePrinScope ωtl
      ξ       = compose
                [ update iCxtEnvL γ
                , update iCxtPrinScopeL ds
                ]
                (ξ₀ θ)
  in do
    rox ← runIM ξ ω xM
    return $ case rox of
      Inl r → Inl r
      Inr (ω' :* o :* x) →
        let ωtl' = update itlStateExpL ω' ωtl in
          Inr $ ωtl' :* o :* x

interpTL ∷ TL → ITLM Val ()
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
        ṽ ← asTLM $ return $ KnownV $ BaseV $ ClearV $ PrinV ρv
        return $ (var ρ ↦ ṽ) :* single ρv
      ArrayPD ρ n → do
        let ρsv = ArrPSV ρ n
        ṽ ← asTLM $ return $ KnownV $ BaseV $ ClearV $ PrinSetV ρsv
        return $ (var ρ ↦ ṽ) :* elimPSV ρsv
    modifyL itlStateEnvL ((dict γρs) ⩌)
    modifyL itlStatePrinScopeL ((concat ρScope) ∪)
  ImportTL path → do
    s ← io $ fread path
    let ts = tokens s
    ls ← io $ tokenizeIO lexer path ts
    tls ← io $ parseIO cpTLs path ls
    interpTLs tls

interpTLs ∷ 𝐿 TL → ITLM Val ()
interpTLs = eachWith interpTL

-- ==== --
-- MAIN --
-- ==== --

evalProgram ∷ IParams → ITLState Val → 𝐿 TL → IO Val
evalProgram θ ω prog = do
  evalITLMIO θ ω "" $ do
    interpTLs prog
    asTLM $ do
      main ← interpVar $ var "main"
      bul  ← return $ KnownV $ BaseV $ ClearV BulV
      evalApp main bul
