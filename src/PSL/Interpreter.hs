module PSL.Interpreter where

import UVMHS
import PSL.Syntax
import PSL.Parser
import PSL.Common

import qualified Prelude as HS

-- mv ∈ mpc-val
data ValMPC =
    BoolMV 𝔹
  | IntMV ℤ
  deriving (Eq,Ord,Show)
makePrettySum ''ValMPC

-- sv ∈ shared-val
data ValS = ValS
  { sharedValRaw ∷ ValMPC
  , sharedValProt ∷ Prot
  , sharedValPrins ∷ 𝑃 Prin
  } deriving (Eq,Ord,Show)
makePrettySum ''ValS

-- v ∈ val
data Val =
    BoolV 𝔹
  | StrV 𝕊
  | IntV ℤ
  | FltV 𝔻
  | BulV
  | LV Val
  | RV Val
  | PairV Val Val
  | NilV
  | ConsV Val Val
  | CloV (𝑂 AVar) APat AExp ICxt
  | TCloV 𝕏 AExp ICxt
  | ShareV ValS
  | ParV (Prin ⇰ Val)
  deriving (Eq,Ord,Show)

-- ṽ ∈ par-val
data ValP =
    BotVP
  | AllVP Val
  | SecVP Prin Val
  | SSecVP (𝑃 Prin) Val
  | ISecVP (Prin ⇰ Val)
  | TopVP
  deriving (Eq,Ord,Show)

isecFrSSec ∷ 𝑃 Prin → Val → Prin ⇰ Val
isecFrSSec ps v = dict $ mapOn (iter ps) $ \ p → p ↦ v

instance Bot ValP where bot = BotVP
instance Join ValP where
  BotVP ⊔ ṽ = ṽ
  ṽ ⊔ BotVP = ṽ
  SecVP p₁ v₁ ⊔ SecVP p₂ v₂ | p₁ ≢ p₂ = ISecVP $ dict $ [p₁ ↦ v₁,p₂ ↦ v₂]
  -- SecVP p₁ v₁ ⊔ SSecVP ps₂ v₂ | p₁ ∉ ps₂ = ISecVP $ (p₁ ↦ v₁) ⩌ isecSSec ps₂ v₂
  -- SSecVP ps₁ v₁ ⊔ SecVP p₂ v₂ | p₂ ∉ ps₁ = ISecVP $ (p₂ ↦ v₂) ⩌ isecSSec ps₁ v₁
  SecVP p₁ v₁ ⊔ ISecVP pvs₂ | p₁ ∉ keys pvs₂ = ISecVP $ (p₁ ↦ v₁) ⩌ pvs₂
  ISecVP pvs₁ ⊔ SecVP p₂ v₂ | p₂ ∉ keys pvs₁ = ISecVP $ (p₂ ↦ v₂) ⩌ pvs₁
  -- SSecVP ps₁ v₁ ⊔ SSecVP ps₂ v₂ | ps₁ ∩ ps₂ ≡ pø = ISecVP $ isecSSec ps₁ v₁ ⩌ isecSSec ps₂ v₂
  -- SSecVP ps₁ v₁ ⊔ ISecVP pvs₂ | ps₁ ∩ keys pvs₂ ≡ pø = ISecVP $ pvs₂ ⩌ isecSSec ps₁ v₁
  -- ISecVP pvs₁ ⊔ SSecVP ps₂ v₂ | keys pvs₁ ∩ ps₂ ≡ pø = ISecVP $ pvs₁ ⩌ isecSSec ps₂ v₂
  ISecVP pvs₁ ⊔ ISecVP pvs₂ | keys pvs₁ ∩ keys pvs₂ ≡ pø = ISecVP $ pvs₁ ⩌ pvs₂
  _ ⊔ _ = TopVP
instance JoinLattice ValP

-- γ ∈ env
type Env = 𝕏 ⇰ ValP

-- σ ∈ state
newtype ITLState = ITLState
  { itlStateEnv ∷ Env 
  } deriving (Eq,Ord,Show)

σtl₀ ∷ ITLState
σtl₀ = ITLState dø

newtype ITLM a = ITLM { unITLM ∷ RWS () () ITLState a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader ()
  ,MonadWriter ()
  ,MonadState ITLState
  )

mkITLM ∷ (ITLState → ITLState ∧ a) → ITLM a
mkITLM f = ITLM $ mkRWS $ \ () σ →
  let σ' :* x = f σ
  in σ' :* () :* x

runITLM ∷ ITLState → ITLM a → ITLState ∧ a
runITLM σ xM =
  let σ' :* () :* x = runRWS () σ $ unITLM xM
  in σ' :* x

evalITLM ∷ ITLState → ITLM a → a
evalITLM σ = snd ∘ runITLM σ

-- ξ ∈ cxt
data ICxt = ICxt
  { iCxtEnv ∷ Env
  , iCxtMode ∷ Mode
  } deriving (Eq,Ord,Show)

ξ₀ ∷ ICxt
ξ₀ = ICxt dø TopM

newtype IM a = IM { unIM ∷ RWS ICxt () () a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader ICxt
  ,MonadWriter ()
  ,MonadState ()
  )

mkIM ∷ (ICxt → a) → IM a
mkIM f = IM $ mkRWS $ \ γ () →
  let x = f γ
  in () :* () :* x

runIM ∷ ICxt → IM a → a
runIM γ xM =
  let () :* () :* x = runRWS γ () $ unIM xM
  in x

asTLM ∷ IM a → ITLM a
asTLM xM = ITLM $ mkRWS $ \ () σ → 
  let () :* () :* x = runRWS (ξ₀ { iCxtEnv = itlStateEnv σ }) () $ unIM xM 
  in σ :* () :* x

makePrettySum ''Val
makePrettySum ''ValP
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''Mode
makePrettySum ''ICxt
makeLenses ''ICxt

----------------------------
-- Variables and Patterns --
----------------------------

interpVar ∷ AVar → IM ValP
interpVar xA = do
  let x = extract xA
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → pptrace (annotatedTag xA) $ error "interpVar: not in scope"

bindVar ∷ AVar → ValP → IM a → IM a
bindVar xA v = 
  let x = extract xA 
  in mapEnvL iCxtEnvL ((x ↦ v) ⩌)

bindPat ∷ APat → ValP → IM a → IM a
bindPat ψA v = case extract ψA of
  VarP x → bindVar x v
  BulP → id
  _ → pptrace (annotatedTag ψA) $ error "bindPat: not implemented"

--------------------
-- Parsing Inputs --
--------------------

parseTy ∷ AType → 𝕊 → Val
parseTy τA s = case extract τA of
  ℤT (Some (64 :* None)) → IntV $ int (HS.read $ chars s ∷ ℤ64)
  _ → error "parseTy: not implemented"

-----------
-- Modes --
-----------

restrictValP ∷ Mode → ValP → ValP
restrictValP m x̃ = case (m,x̃) of
  (TopM,_) → x̃
  (_,TopVP) → TopVP
  (BotM,_) → BotVP
  (_,BotVP) → BotVP
  (SecM p,AllVP v) → SecVP p v
  (SecM p,SecVP p' v) | p ≡ p' → SecVP p' v
  (SecM p,SSecVP ps v) | p ∈ ps → SecVP p v
  (SecM p,ISecVP pvs) | p ∈ keys pvs → SecVP p $ pvs ⋕! p
  (SSecM ps,AllVP v) → SSecVP ps v
  (SSecM ps,SecVP p' v) | p' ∈ ps → SecVP p' v
  (SSecM ps,SSecVP ps' v) → SSecVP (ps ∩ ps') v
  (SSecM ps,ISecVP pvs) → ISecVP $ restrict ps pvs
  (_,_) → BotVP

restrictMode ∷ Mode → IM ValP → IM ValP
restrictMode m xM = do
  m' ← askL iCxtModeL
  ṽ ← localL iCxtModeL (m ⊓ m') xM
  return $ restrictValP m ṽ

---------------------
-- Parallel Values --
---------------------

bindValP ∷ ValP → (Val → IM ValP) → IM ValP
bindValP ṽ f = case ṽ of
  BotVP → return BotVP
  AllVP v → f v
  SecVP p v → restrictMode (SecM p) $ f v
  SSecVP ps v → restrictMode (SSecM ps) $ f v
  ISecVP pvs → 
    joins ^$ mapMOn (iter pvs) $ \ (p :* v) →
      restrictMode (SecM p) $ f v
  TopVP → error "bindValP: ṽ = TopVP"

bindValsPR ∷ 𝐼 Val → 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
bindValsPR vs ṽs f = case ṽs of
  Nil → f $ list vs
  ṽ :& ṽs' → bindValP ṽ $ \ v → bindValsPR (vs ⧺ single v) ṽs' f

bindValsP ∷ 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
bindValsP = bindValsPR null

--------------------------
-- Primitive Operations --
--------------------------

interpPrimRaw ∷ 𝕊 → 𝐿 Val → Val
interpPrimRaw "LTE" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≤ i₂
interpPrimRaw "PLUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ + i₂
interpPrimRaw "EQ" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≡ i₂
interpPrimRaw s vs = pptrace s $ pptrace vs $ error "interpPrimRaw: not implemented"

mpcFrVal ∷ Val → ValMPC
mpcFrVal (BoolV b) = BoolMV b
mpcFrVal (IntV i) = IntMV i
mpcFrVal _ = error "mpcFrVal"

valFrMPC ∷ ValMPC → Val
valFrMPC (BoolMV b) = BoolV b
valFrMPC (IntMV i) = IntV i

rawShareOps ∷ 𝑃 𝕊
rawShareOps = pow
  [ "LTE"
  , "PLUS"
  , "EQ"
  ]

onRawShareVals ∷ Prot → 𝑃 Prin → 𝐼 Val → (𝐿 Val → Val) → 𝐿 Val → Val
onRawShareVals φ ps vs f = \case
  Nil → ShareV $ ValS (mpcFrVal $ f $ list vs) φ ps
  ShareV (ValS v φ' ps') :& vs' | (φ ≡ φ') ⩓ (ps ≡ ps') → onRawShareVals φ ps (vs ⧺ single (valFrMPC v)) f vs'
  _ → error "error"

onRawVals ∷ (𝐿 Val → Val) → 𝐿 Val → Val
onRawVals f vs = case vs of
  ShareV (ValS _ φ ps) :& _ → onRawShareVals φ ps null f vs
  _ → f vs

interpPrim ∷ 𝕊 → 𝐿 Val → Val
interpPrim = onRawVals ∘ interpPrimRaw

-----------------
-- Expressions --
-----------------

interpExp ∷ AExp → IM ValP
interpExp eA = case extract eA of
  VarE x → interpVar x
  -- BoolE
  StrE s → return $ AllVP $ StrV s
  IntE i → return $ AllVP $ IntV i
  -- FltE
  BulE → return $ AllVP $ BulV
  IfE e₁ e₂ e₃ → do
    ṽ ← interpExp e₁
    bindValP ṽ $ \ v → do
      case v of
        BoolV b 
          | b ≡ True → interpExp e₂
          | b ≡ False → interpExp e₃
        _ → error "interpExp: IfE: v ≢ BoolV _"
  -- LE
  -- RE
  TupE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    bindValP ṽ₁ $ \ v₁ →
      bindValP ṽ₂ $ \ v₂ →
        return $ AllVP $ PairV v₁ v₂
  -- NilE
  -- ConsE
  LetTyE _ _ e → interpExp e
  LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  -- CaseE
  LamE selfO ψ e → do
    ξ ← ask
    return $ AllVP $ CloV selfO ψ e ξ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    bindValP ṽ₁ $ \ v₁ → case v₁ of
      CloV selfO ψ e ξ → do
        let selfγ = case selfO of
              None → id
              Some self → bindVar self ṽ₁
        compose [local ξ,bindPat ψ ṽ₂,selfγ ] $ interpExp e
      _ → pptrace (annotatedTag eA) $ error "interpExp: AppE: v₁ ≢ CloV _ _ _ _"
  -- TLamE
  -- TAppE
  SoloE pA e → do
    let p = extract pA
    restrictMode (SecM p) $ interpExp e
  ParE psA e → do
    let ps = extractPrins psA
    joins ^$ mapMOn (iter ps) $ \ p → do restrictMode (SecM p) $ interpExp e
  ShareE φA psA e → do
    let φ = extract φA
    let ps = extractPrins psA
    ṽ ← interpExp e
    return $ case ṽ of
      AllVP v → case v of
        BoolV b → AllVP $ ShareV $ ValS (BoolMV b) φ ps
        IntV i → AllVP $ ShareV $ ValS (IntMV i) φ ps
        _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: AllVP: v ∉ {BoolV _,IntV _}"
      SecVP _p v → case v of
        BoolV b → AllVP $ ShareV $ ValS (BoolMV b) φ ps
        IntV i → AllVP $ ShareV $ ValS (IntMV i) φ ps
        _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: SecVP: v ∉ {BoolV _,IntV _}"
      _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: ṽ ≢ SecVP _ _"
  AccessE e pA → do
    let p = extract pA
    ṽ ← interpExp e
    return $ case ṽ of
      ISecVP pvs → case pvs ⋕? p of
        Some v → SecVP p v
        _ → error "interpExp: AccessE: ISecVP: pvs ⋕? p ≢ Some v"
      _ → error "interpExp: AccessE: ṽ ≢ ISecVP _"
  BundleE pes → do
    joins ^$ mapMOn (iter pes) $ \ (pA :* e) → do
      let p = extract pA
      restrictMode (SecM p) $ interpExp e
  -- BundleUnionE
  RevealE psA e → do
    let ps = extractPrins psA
    ṽ ← interpExp e
    case ṽ of
      AllVP v → return $ SSecVP ps $ case v of
        (ShareV (ValS (BoolMV b) _ _)) → BoolV b
        (ShareV (ValS (IntMV i) _ _)) → IntV i
        _ → pptrace (annotatedTag eA) $ error "interpExp: RevealE: v ∉ {ShaveV (ValS (BoolMV _) _ _),ShareV (ValS (IntMV _) _ _)}"
      _ → pptrace (annotatedTag eA) $ error "interpExp: RevealE: ṽ ≢ AllVP _"
  -- AscrE
  ReadE τA e → do
    ṽ ← interpExp e
    bindValP ṽ $ \ v → case v of
      StrV fn → do
        m ← askL iCxtModeL
        return $ case m of
          TopM → error "cannot read at top level, must be in solo or par mode"
          SecM p → AllVP $ parseTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name p ⧺ "/" ⧺ fn
          SSecM _ → error "cannot read in shared secret mode"
          BotM → error "cannot read in bot mode"
      _ → error "interpExp: ReadE: v ≢ StrV _"
  -- InferE
  -- HoleE
  PrimE o es → do
    ṽs ← mapM interpExp es
    bindValsP ṽs $ \ vs → return $ AllVP $ interpPrim o vs
  _ → pptrace (annotatedTag eA) $ error "not implemented: interpExp"

--------------------------
-- Top-level Statements --
--------------------------

interpTL ∷ ATL → ITLM ()
interpTL sA = case extract sA of
  DeclTL _ _ _ → skip
  DefnTL xA e → do
    let x = extract xA
    v ← asTLM $ interpExp e
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL _ → skip
  _ → pptrace (annotatedTag sA) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 ATL → ITLM ()
interpTLs = eachWith interpTL

-------------
-- Testing --
-------------

interpretExample ∷ 𝕊 → IO ValP
interpretExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  s ← read path
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  -- out $ "DONE PARSING:" ⧺ fn
  let σtl = evalITLM σtl₀ $ retState $ interpTLs tls
  return $ itlStateEnv σtl ⋕! var "main"

testInterpreterExample ∷ 𝕊 → IO ()
testInterpreterExample fn = pprint *$ interpretExample fn

tests ∷ 𝐿 (𝕊 ∧ ValP)
tests = frhs
 [ ("micro-let",AllVP (IntV $ int 2))
 ]

testInterpreter ∷ IO ()
testInterpreter = do
  pprint $ ppVertical
    [ ppHeader "TESTS"
    , concat
      [ ppSpace $ 𝕟64 2
      , ppAlign $ concat $ mapOn tests $ \ (fn :* v) → 
          let rV = ioUNSAFE $ interpretExample fn
          in
          ppVertical
           [ ppHorizontal [ppHeader "FILE:",pretty fn]
           , concat
               [ ppSpace $ 𝕟64 2
               , ppAlign $ ppVertical
                   [ ppHorizontal [ppHeader "RETURNED:",pretty rV]
                   , ppHorizontal [ppHeader "EXPECTED:",pretty v]
                   , ppHorizontal [ppHeader "PASSED:",pretty $ rV ≡ v]
                   ]
               ]
           ]
      ]
    ]
  testInterpreterExample "cmp"
  testInterpreterExample "cmp-tutorial"
  testInterpreterExample "euclid"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"
