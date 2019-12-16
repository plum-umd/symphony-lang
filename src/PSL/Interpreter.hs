module PSL.Interpreter where

import UVMHS
import PSL.Parser
import PSL.Syntax

import PSL.Data.Mode

import qualified PSL.SyntaxUF as UF

import qualified Prelude as HS

{-

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
  | CloV (𝑂 UF.Var) UF.Pat UF.Exp ICxt
  | TCloV UF.TVar UF.Exp ICxt
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

-- γ ∈ ienv
type Env = 𝕏 ⇰ ValP

-- σ ∈ itlstate
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

interpVar ∷ Var → IM ValP
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → pptrace (annotatedTag xA) $ error "interpVar: not in scope"

bindVar ∷ Var → ValP → IM a → IM a
bindVar x v = mapEnvL iCxtEnvL ((x ↦ v) ⩌)

bindPat ∷ UF.Pat → ValP → IM a → IM a
bindPat ψˢ v = case extract ψˢ of
  UF.VarP x → bindVar x v
  UF.BulP → id
  _ → pptrace (annotatedTag ψˢ) $ error "bindPat: not implemented"

--------------------
-- Parsing Inputs --
--------------------

parseTy ∷ UF.Type → 𝕊 → Val
parseTy τA s = case extract τA of
  UF.ℤT (Some (64 :* None)) → IntV $ int (HS.read $ chars s ∷ ℤ64)
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
interpPrimRaw "OR" (tohs → [BoolV b₁,BoolV b₂]) = BoolV $ b₁ ⩔ b₂
interpPrimRaw "AND" (tohs → [BoolV b₁,BoolV b₂]) = BoolV $ b₁ ⩓ b₂
interpPrimRaw "PLUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ + i₂
interpPrimRaw "MINUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ - i₂
interpPrimRaw "TIMES" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ × i₂
interpPrimRaw "DIV" (tohs → [IntV i₁,IntV i₂]) = IntV $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
interpPrimRaw "MOD" (tohs → [IntV i₁,IntV i₂]) = IntV $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
interpPrimRaw "EQ" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≡ i₂
interpPrimRaw "LT" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ < i₂
interpPrimRaw "GT" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ > i₂
interpPrimRaw "LTE" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≤ i₂
interpPrimRaw "GTE" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≥ i₂
interpPrimRaw "COND" (tohs → [BoolV b,v₁,v₂]) = if b then v₁ else v₂
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
  [ "LT"
  , "GT"
  , "LTE"
  , "GTE"
  , "PLUS"
  , "MINUS"
  , "TIMES"
  , "DIV"
  , "MOD"
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

interpExp ∷ UF.Exp → IM ValP
interpExp eA = case extract eA of
  UF.VarE x → interpVar x
  -- BoolE
  UF.StrE s → return $ AllVP $ StrV s
  UF.IntE i → return $ AllVP $ IntV i
  -- FltE
  UF.BulE → return $ AllVP $ BulV
  UF.IfE e₁ e₂ e₃ → do
    ṽ ← interpExp e₁
    bindValP ṽ $ \ v → do
      case v of
        BoolV b 
          | b ≡ True → interpExp e₂
          | b ≡ False → interpExp e₃
        _ → error "interpExp: IfE: v ≢ BoolV _"
  -- LE
  -- RE
  UF.TupE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    bindValP ṽ₁ $ \ v₁ →
      bindValP ṽ₂ $ \ v₂ →
        return $ AllVP $ PairV v₁ v₂
  -- NilE
  -- ConsE
  UF.LetTyE _ _ e → interpExp e
  UF.LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  -- CaseE
  UF.LamE selfO ψ e → do
    ξ ← ask
    return $ AllVP $ CloV selfO ψ e ξ
  UF.AppE e₁ e₂ → do
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
  UF.SoloE pA e → do
    let p = extract pA
    restrictMode (SecM p) $ interpExp e
  UF.ParE psA e → do
    let ps = map strip psA
    joins ^$ mapMOn (iter ps) $ \ p → do restrictMode (SecM p) $ interpExp e
  UF.ShareE φA psA e → do
    let φ = strip φA
    let ps = pow $ map strip psA
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
  UF.AccessE e pA → do
    let p = extract pA
    ṽ ← interpExp e
    return $ case ṽ of
      ISecVP pvs → case pvs ⋕? p of
        Some v → SecVP p v
        _ → error "interpExp: AccessE: ISecVP: pvs ⋕? p ≢ Some v"
      _ → error "interpExp: AccessE: ṽ ≢ ISecVP _"
  UF.BundleE pes → do
    joins ^$ mapMOn (iter pes) $ \ (pA :* e) → do
      let p = extract pA
      restrictMode (SecM p) $ interpExp e
  -- BundleUnionE
  UF.RevealE psA e → do
    let ps = pow $ map strip psA
    ṽ ← interpExp e
    case ṽ of
      AllVP v → return $ SSecVP ps $ case v of
        (ShareV (ValS (BoolMV b) _ _)) → BoolV b
        (ShareV (ValS (IntMV i) _ _)) → IntV i
        _ → pptrace (annotatedTag eA) $ error "interpExp: RevealE: v ∉ {ShaveV (ValS (BoolMV _) _ _),ShareV (ValS (IntMV _) _ _)}"
      _ → pptrace (annotatedTag eA) $ error "interpExp: RevealE: ṽ ≢ AllVP _"
  -- AscrE
  UF.ReadE τA e → do
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
  UF.PrimE o es → do
    ṽs ← mapM interpExp es
    bindValsP ṽs $ \ vs → return $ AllVP $ interpPrim o vs
  UF.TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  _ → pptrace (annotatedTag eA) $ error "interpExp: not implemented"

--------------------------
-- Top-level Statements --
--------------------------

interpTL ∷ UF.TL → ITLM ()
interpTL tlA = case extract tlA of
  UF.DefnTL xA ψs e →  do
    let x = extract xA
    let e' = UF.buildLambda (annotatedTag tlA) xA ψs e
    v ← asTLM $ interpExp e'
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  _ → pptrace (annotatedTag tlA) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 UF.TL → ITLM ()
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
  testInterpreterExample "euclid2"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"

-}
