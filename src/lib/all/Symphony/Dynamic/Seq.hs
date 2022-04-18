module Symphony.Dynamic.Seq where

import Symphony.Prelude

import Symphony.Config
import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Seq.ReadType
import Symphony.Dynamic.Seq.Types
import Symphony.Dynamic.Seq.Seq.Types
import Symphony.Dynamic.Seq.Seq.Val
import Symphony.Dynamic.Seq.Operations
import Symphony.Dynamic.Seq.BaseVal
import Symphony.Dynamic.Seq.Lens
import Symphony.Dynamic.Seq.Error

import qualified Prelude as HS
import qualified Crypto.Random as R
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Binary as B
import GHC.RTS.Flags (RTSFlags(profilingFlags))

--import Foreign.ForeignPtr

-----------------------------
--- Principal Expressions ---
-----------------------------

interpPrinExp ∷ (STACK) ⇒ PrinExp → IM SeqVal PrinVal
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

interpPrinSetExp ∷ (STACK) ⇒ PrinSetExp → IM SeqVal PrinSetVal
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

interpVar ∷ (STACK) ⇒ Var → IM SeqVal SeqVal
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

interpBul ∷ (STACK) ⇒ IM SeqVal SeqVal
interpBul = introVal $ BaseV $ Clear BulV

interpBool ∷ (STACK) ⇒ 𝔹 → IM SeqVal SeqVal
interpBool b = introVal $ BaseV $ Clear $ BoolV b

interpNat ∷ (STACK) ⇒ IPrecision → ℕ → IM SeqVal SeqVal
interpNat pr n = introVal $ BaseV $ Clear $ NatV pr n

interpInt ∷ (STACK) ⇒ IPrecision → ℤ → IM SeqVal SeqVal
interpInt pr z = introVal $ BaseV $ Clear $ IntV pr z

interpFlt ∷ (STACK) ⇒ FPrecision → 𝔻 → IM SeqVal SeqVal
interpFlt pr d = introVal $ BaseV $ Clear $ FltV pr d

interpStr ∷ (STACK) ⇒ 𝕊 → IM SeqVal SeqVal
interpStr s = introVal $ BaseV $ Clear $ StrV s

interpPrin ∷ (STACK) ⇒ PrinExp → IM SeqVal SeqVal
interpPrin ρe =
  let c = interpPrinExp ρe
  in do
    ρv ← c
    introVal $ BaseV $ Clear $ PrinV ρv

interpPrinSet ∷ (STACK) ⇒ PrinSetExp → IM SeqVal SeqVal
interpPrinSet ρse =
  let c = interpPrinSetExp ρse
  in do
    ρsv ← c
    introVal $ BaseV $ Clear $ PrinSetV ρsv

interpPrim ∷ (STACK) ⇒ Op → 𝐿 Exp → IM SeqVal SeqVal
interpPrim op es =
  let cs = map interpExp es
  in do
    primVal op *$ exchange cs

---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

interpProd ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
interpProd eₗ eᵣ =
  let cₗ = interpExp eₗ
      cᵣ = interpExp eᵣ
  in do
    ṽₗ ← cₗ
    ṽᵣ ← cᵣ
    introVal $ ProdV ṽₗ ṽᵣ

interpL ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpL eₗ =
  let cₗ = interpExp eₗ
  in do
    bvₜ ← introClear $ BoolV True
    ṽₗ  ← cₗ
    ṽᵣ  ← interpDefault
    introVal $ SumV bvₜ ṽₗ ṽᵣ

interpR ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpR eᵣ =
  let cᵣ = interpExp eᵣ
  in do
    bvₜ ← introClear $ BoolV False
    ṽₗ  ← interpDefault
    ṽᵣ  ← cᵣ
    introVal $ SumV bvₜ ṽₗ ṽᵣ

interpNil ∷ (STACK) ⇒ IM SeqVal SeqVal
interpNil = introVal $ ListV Nil

interpCons ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
interpCons eₕ eₜ =
  let cₕ = interpExp eₕ
      cₜ = interpExp eₜ
  in do
    ṽ  ← cₕ
    ṽs ← elimList *$ elimVal *⋅ cₜ
    introVal $ ListV $ ṽ :& ṽs

interpIf ∷ (STACK) ⇒ Exp → Exp → Exp → IM SeqVal SeqVal
interpIf e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
    b ← elimBool *$ elimClear *$ elimBase *$ elimVal *⋅ c₁
    if b then c₂ else c₃

interpCase ∷ (STACK) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM SeqVal SeqVal
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

interpLet ∷ (STACK) ⇒ Pat → Exp → Exp → IM SeqVal SeqVal
interpLet ψ e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    ṽ₁ ← c₁
    f  ← bindVal ṽ₁ ψ
    f c₂

interpLam ∷ (STACK) ⇒ 𝑂 Var → 𝐿 Pat → Exp → IM SeqVal SeqVal
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

evalApp ∷ (STACK) ⇒ SeqVal → SeqVal → IM SeqVal SeqVal
evalApp ṽ₁ ṽ₂ = do
  self𝑂 :* f₁ ← elimClo *$ elimVal ṽ₁
  let selfγ = case self𝑂 of
                None      → id
                Some self → bindTo self ṽ₁
  f₁ selfγ ṽ₂

interpApp ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
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

interpRead ∷ (STACK) ⇒ Type → Exp → IM SeqVal SeqVal
interpRead τ e =
  let c = interpExp e
  in do
    fn ← elimStr *$ elimClear *$ elimBase *$ elimVal *⋅ c
    ρ  ← singletonMode
    path ← inputPath ρ fn
    deserializeVal τ *$ io $ fread path

interpWrite ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
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

interpTrace ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
interpTrace e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    pptraceM *⋅ c₁
    c₂

------------------
--- References ---
------------------

interpRef ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpRef e =
  let c₁ = interpExp e
  in do
  ṽ ← c₁
  r ← io $ newℝMut ṽ
  introVal *$ introLoc (Inl r)

interpRefRead ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpRefRead e =
  let c₁ = interpExp e
  in do
  r ← elimRef *$ elimLocRead *$ elimVal *⋅ c₁
  ṽᵣ ← io $ readℝMut r
  locateVal ṽᵣ

interpRefWrite ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
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

interpArray ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
interpArray e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
  _pr :* n ← elimNat *$ elimClear *$ elimBase *$ elimVal *⋅ c₁
  ṽ₂ ← c₂
  a  ← io $ vecIMut $ replicate n ṽ₂
  introVal *$ introLoc (Inr a)

interpArrayRead ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
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

interpArrayWrite ∷ (STACK) ⇒ Exp → Exp → Exp → IM SeqVal SeqVal
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

interpArraySize ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpArraySize e = do
  a ← elimArr *$ elimLocRead *$ elimVal *$ interpExp e
  interpNat iprDefault $ nat $ length𝕍Mut a

-----------
--- Par ---
-----------

interpPar ∷ (STACK) ⇒ PrinSetExp → Exp → IM SeqVal SeqVal
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

interpRand ∷ (STACK) ⇒ PrinSetExp → BaseType → IM SeqVal SeqVal
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

modeCheckComm ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM v ()
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

interpShare ∷ (STACK) ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → IM SeqVal SeqVal
interpShare φ τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsFr ρvsTo
    shareValSeq φ ρvsFr ρvsTo ṽ τ

interpReveal ∷ (STACK) ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → IM SeqVal SeqVal
interpReveal φ τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsTo ρvsFr
    revealValSeq φ ρvsFr ρvsTo ṽ τ

interpComm ∷ (STACK) ⇒ Type → PrinSetExp → PrinSetExp → Exp → IM SeqVal SeqVal
interpComm τ ρse₁ ρse₂ e₃ =
  let c₁ = interpPrinSetExp ρse₁
      c₂ = interpPrinSetExp ρse₂
      c₃ = interpExp e₃
  in do
    ρvsFr ← elimPSV ^$ c₁
    ρvsTo ← elimPSV ^$ c₂
    ṽ     ← c₃
    modeCheckComm ρvsFr ρvsTo
    commValSeq ρvsFr ρvsTo ṽ τ

----------------------
--- MPC Operations ---
----------------------

interpMuxIf ∷ (STACK) ⇒ Exp → Exp → Exp → IM SeqVal SeqVal
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

interpMuxCase ∷ (STACK) ⇒ Exp → 𝐿 (Pat ∧ Exp) → IM SeqVal SeqVal
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

interpProc ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpProc e =
  let c = interpExp e
  in do
    κ :* v₀ ←
      localizeL iStateMPCContL null $
      localL iCxtMPCPathConditionL null $
      c
    mfoldrOnFrom (reverse κ) v₀ $ \ (pcᴿ :* v₁) v₂ → mfoldrOnFrom pcᴿ v₁ $ \ vᵖᶜ acc → muxVal vᵖᶜ acc v₂

interpReturn ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
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

interpBundle ∷ (STACK) ⇒ 𝐿 (PrinExp ∧ Exp) → IM SeqVal SeqVal
interpBundle ρee𝐿 =
  let cc𝐿 = map (mapPair interpPrinExp interpExp) ρee𝐿
  in
  introVal *$ BundleV ^$ dict ^$ mapMOn (iter cc𝐿) $ \ (c₁ :* c₂) → do
    ρ ← c₁
    ṽ ← c₂
    return $ ρ ↦ ṽ

interpBundleAccess ∷ (STACK) ⇒ Exp → PrinExp → IM SeqVal SeqVal
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

interpBundleUnion ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
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

interpSeq ∷ (STACK) ⇒ Exp → Exp → IM SeqVal SeqVal
interpSeq e₁ e₂ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
  in do
    _ ← c₁
    c₂

---------------
--- Default ---
---------------

interpDefault ∷ (STACK) ⇒ IM SeqVal SeqVal
interpDefault = introVal DefaultV

-------------------
--- Expressions ---
-------------------

--wrapInterp ∷ (STACK) ⇒ (ExpR → IM v a) → Exp → IM v a
--wrapInterp f e = localL iCxtSourceL (Some $ atag e) $ f $ extract e

interpExp ∷ (STACK) ⇒ Exp → IM SeqVal SeqVal
interpExp e = localL iCxtSourceL (Some $ atag e) $ interpExpR $ extract e

interpExpR ∷ (STACK) ⇒ ExpR → IM SeqVal SeqVal
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
  ShareE φ τ ρse₁ ρse₂ e₃  → interpShare φ τ ρse₁ ρse₂ e₃
  RevealE φ τ ρse₁ ρse₂ e₃ → interpReveal φ τ ρse₁ ρse₂ e₃
  SendE τ ρe₁ ρse₂ e₃      → interpComm τ ρe₁ ρse₂ e₃

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

asTLM ∷ IM SeqVal a → ITLM SeqVal a
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

interpTL ∷ TL → ITLM SeqVal ()
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

interpTLs ∷ 𝐿 TL → ITLM SeqVal ()
interpTLs = eachWith interpTL

-- ==== --
-- MAIN --
-- ==== --

evalProgram ∷ IParams → ITLState SeqVal → 𝐿 TL → IO SeqVal
evalProgram θ ω prog = do
  evalITLMIO θ ω "" $ do
    interpTLs prog
    asTLM $ do
      main ← interpVar $ var "main"
      bul  ← introVal $ BaseV $ Clear BulV
      evalApp main bul
