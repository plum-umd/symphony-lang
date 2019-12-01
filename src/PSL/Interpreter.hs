module PSL.Interpreter where

import UVMHS
import PSL.Syntax
import PSL.Parser

import qualified Prelude as HS

-- c ∈ circuit
data Circ =
    BoolC (𝑂 (Prin ∨ Scheme)) 𝔹
  | IntC (𝑂 (Prin ∨ Scheme)) ℤ
  | OpC 𝕊 (𝐿 Circ)
  deriving (Eq,Ord,Show)
makePrettySum ''Circ

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
  | CircV Circ
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

isecSSec ∷ 𝑃 Prin → Val → Prin ⇰ Val
isecSSec ps v = dict $ mapOn (iter ps) $ \ p → p ↦ v

instance Bot ValP where bot = BotVP
instance Join ValP where
  BotVP ⊔ ṽ = ṽ
  ṽ ⊔ BotVP = ṽ
  SecVP p₁ v₁ ⊔ SecVP p₂ v₂ | p₁ ≢ p₂ = ISecVP $ dict $ [p₁ ↦ v₁,p₂ ↦ v₂]
  SecVP p₁ v₁ ⊔ SSecVP ps₂ v₂ | p₁ ∉ ps₂ = ISecVP $ (p₁ ↦ v₁) ⩌ isecSSec ps₂ v₂
  SSecVP ps₁ v₁ ⊔ SecVP p₂ v₂ | p₂ ∉ ps₁ = ISecVP $ (p₂ ↦ v₂) ⩌ isecSSec ps₁ v₁
  SecVP p₁ v₁ ⊔ ISecVP pvs₂ | p₁ ∉ keys pvs₂ = ISecVP $ (p₁ ↦ v₁) ⩌ pvs₂
  ISecVP pvs₁ ⊔ SecVP p₂ v₂ | p₂ ∉ keys pvs₁ = ISecVP $ (p₂ ↦ v₂) ⩌ pvs₁
  SSecVP ps₁ v₁ ⊔ SSecVP ps₂ v₂ | ps₁ ∩ ps₂ ≡ pø = ISecVP $ isecSSec ps₁ v₁ ⩌ isecSSec ps₂ v₂
  SSecVP ps₁ v₁ ⊔ ISecVP pvs₂ | ps₁ ∩ keys pvs₂ ≡ pø = ISecVP $ pvs₂ ⩌ isecSSec ps₁ v₁
  ISecVP pvs₁ ⊔ SSecVP ps₂ v₂ | keys pvs₁ ∩ ps₂ ≡ pø = ISecVP $ pvs₁ ⩌ isecSSec ps₂ v₂
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
  , iCxtMode ∷ 𝑂 (𝑃 Prin)
  } deriving (Eq,Ord,Show)

ξ₀ ∷ ICxt
ξ₀ = ICxt dø None

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
makePrettySum ''ICxt
makeLenses ''ICxt

--------------
-- Circuits --
--------------

interpCirc ∷ Circ → 𝔹 ∨ ℤ
interpCirc = \case
  BoolC _ b → Inl b
  IntC _ i → Inr i 
  OpC "PLUS" (tohs → [c₁,c₂]) →
    let Inr i₁ = interpCirc c₁ 
        Inr i₂ = interpCirc c₂
    in Inr $ i₁ + i₂
  OpC "LTE" (tohs → [c₁,c₂]) →
    let Inr i₁ = interpCirc c₁ 
        Inr i₂ = interpCirc c₂
    in Inl $ i₁ ≤ i₂
  _ → error "interpCir: bad circuit"

-----------------
-- MPC results --
-----------------

schemeProt ∷ Prot → Scheme
schemeProt = \case
  YaoP → YaoS
  BGWP → ShamirS
  GMWP → GMWS
    
----------------------------
-- Variables and Patterns --
----------------------------

interpVar ∷ AVar → IM ValP
interpVar xA = do
  let x = extract xA
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → error "interpVar: not in scope"

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

intersectModes ∷ 𝑂 (𝑃 Prin) → 𝑂 (𝑃 Prin) → 𝑂 (𝑃 Prin)
intersectModes psO₁ psO₂ = case (psO₁,psO₂) of
  (None,_) → psO₂
  (_,None) → psO₁
  (Some ps₁,Some ps₂) → Some $ ps₁ ∩ ps₂

restrictValP ∷ 𝑂 (𝑃 Prin) → ValP → ValP
restrictValP m x̃ = case (m,x̃) of
  (None,_) → x̃
  (Some _,BotVP) → BotVP
  (Some ps,AllVP v) → SSecVP ps v
  (Some ps,SecVP p v) 
    | p ∈ ps → SecVP p v
    | otherwise → BotVP
  (Some ps,SSecVP ps' v) → SSecVP (ps ∩ ps') v
  (Some ps,ISecVP pvs) → ISecVP $ restrict ps pvs
  (Some _,TopVP) → TopVP

restrictMode ∷ 𝑂 (𝑃 Prin) → IM ValP → IM ValP
restrictMode m xM = do
  m' ← askL iCxtModeL
  ṽ ← localL iCxtModeL (intersectModes m m') xM
  return $ restrictValP m ṽ

---------------------
-- Parallel Values --
---------------------

bindValP ∷ ValP → (Val → IM ValP) → IM ValP
bindValP ṽ f = case ṽ of
  BotVP → return BotVP
  AllVP v → f v
  SecVP p v → restrictMode (Some $ single p) $ f v
  SSecVP ps v → restrictMode (Some ps) $ f v
  ISecVP pvs → 
    joins ^$ mapMOn (iter pvs) $ \ (p :* v) →
      restrictMode (Some $ single p) $ f v
  TopVP → error "bindValP: ṽ = TopVP"

-----------------
-- Expressions --
-----------------

interpExp ∷ AExp → IM ValP
interpExp eA = case extract eA of
  VarE x → interpVar x
  -- BoolE
  StrE s → return $ AllVP $ StrV s
  -- IntE
  -- FltE
  BulE → return $ AllVP $ BulV
  -- IfE
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
    restrictMode (Some $ single p) $ interpExp e
  ParE psA e → do
    let ps = pow $ map extract $ iter $ extract psA
    joins ^$ mapMOn (iter ps) $ \ p → do
      restrictMode (Some $ single p) $ interpExp e
  CirE e → do
    ṽ ← interpExp e
    return $ AllVP $ CircV $ case ṽ of
      SecVP p v → case v of
        BoolV b → BoolC (Some $ Inl p) b
        IntV i → IntC (Some $ Inl p) i
        _ → pptrace (annotatedTag eA) $ error "interpExp: CirE: SecVP: v ∉ {BoolV _,IntV _}"
      _ → pptrace (annotatedTag eA) $ pptrace ṽ $ error "interpExp: CirE: ṽ ≢ SecVP _ _"
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
      restrictMode (Some $ single p) $ interpExp e
  -- BundleUnionE
  -- DelegateE
  MPCE φA psA e → do
    let φ = extract φA
    let ps = pow $ map extract $ iter $ extract psA
    ṽ ← interpExp e
    let v = case ṽ of
          AllVP v' → v'
          SSecVP ps' v'
            | ps ⊆ ps' → v'
            | otherwise → error "interpExp: MPCE: SSec: ps ⊈ ps'"
          _ → error "interpExp: MPCE: ṽ ∉ {AllVP _,SSec _ _}"
    return $ AllVP $ CircV $ case v of
      CircV c → case interpCirc c of
        Inl b → BoolC (Some $ Inr $ schemeProt φ) b
        Inr i → IntC (Some $ Inr $ schemeProt φ) i
      _ → error "interpExp: MPCE: v ≢ CircV _"
  RevealE psA e → do
    let ps = pow $ map extract $ iter $ extract psA
    ṽ ← interpExp e
    case ṽ of
      AllVP v → return $ SSecVP ps $ case v of
        CircV (BoolC (Some (Inr _)) b) → BoolV b
        CircV (IntC (Some (Inr _)) i) → IntV i
        _ → error "interpExp: RevealE: v ∉ {BoolC _,IntC i}"
      _ → error "interpExp: RevealE: ṽ ≢ AllVP _"
  -- AscrE
  ReadE τA e → do
    ṽ ← interpExp e
    bindValP ṽ $ \ v → case v of
      StrV fn → do
        m ← askL iCxtModeL
        return $ case m of
          None → error "cannot read at top level, must be in solo or par mode"
          Some ps →
            joins $ mapOn (iter ps) $ \ p →
              SecVP p $ parseTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name p ⧺ "/" ⧺ fn
      _ → error "interpExp: ReadE: v ≢ StrV _"
  -- InferE
  -- HoleE
  PrimE "LTE" (tohs → [e₁,e₂]) → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    bindValP ṽ₁ $ \ v₁ →
      bindValP ṽ₂ $ \ v₂ →
        return $ AllVP $ case (v₁,v₂) of
          (IntV i₁,IntV i₂) → IntV $ i₁ + i₂
          (CircV c₁,CircV c₂) → CircV $ OpC "LTE" $ list [c₁,c₂]
          (_,_) → error "interpExp: PrimE: not implemented, or bad prim application"
  _ → pptrace (annotatedTag eA) $ error "not implemented: interpExp"

--------------------------
-- Top-level Statements --
--------------------------

interpTL ∷ ATL → ITLM ()
interpTL sA = case extract sA of
  DeclTL _ _ → skip
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

testInterpreterExample ∷ 𝕊 → IO ()
testInterpreterExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  s ← read path
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  -- out $ "DONE PARSING:" ⧺ fn
  let σtl = evalITLM σtl₀ $ retState $ interpTLs tls
  pprint $ itlStateEnv σtl ⋕! var "main"

testInterpreter ∷ IO ()
testInterpreter = do
  testInterpreterExample "cmp"
  testInterpreterExample "cmp-split"
  testInterpreterExample "cmp-tutorial"
