module PSL.Interpreter where

import UVMHS
import PSL.Syntax
import PSL.Parser

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
  -- SecVP p₁ v₁ ⊔ ISecVP pvs₂ | p₁ ∉ keys pvs₂ = ISecVP $ (p₁ ↦ v₁) ⩌ pvs₂
  -- ISecVP pvs₁ ⊔ SecVP p₂ v₂ | p₂ ∉ keys pvs₁ = ISecVP $ (p₂ ↦ v₂) ⩌ pvs₁
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

-- m ∈ mode
data Mode =
    TopM
  | SecM Prin
  | SSecM (𝑃 Prin)
  | BotM
  deriving (Eq,Ord,Show)

instance Top Mode where top = TopM
instance Bot Mode where bot = BotM
instance Join Mode where
  m₁ ⊔ m₂ | m₁ ≡ m₂ = m₁
  BotM ⊔ m = m
  m ⊔ BotM = m
  SSecM ps₁ ⊔ SSecM ps₂ = SSecM $ ps₁ ∪ ps₂
  _ ⊔ _ = TopM
instance Meet Mode where
  m₁ ⊓ m₂ | m₁ ≡ m₂ = m₁
  TopM ⊓ m = m
  m ⊓ TopM = m
  SSecM ps₁ ⊓ SSecM ps₂ = SSecM $ ps₁ ∩ ps₂
  _ ⊓ _ = BotM
instance JoinLattice Mode
instance MeetLattice Mode
instance Lattice Mode

instance POrd Mode where m₁ ⊑ m₂ = (m₁ ⊔ m₂) ≡ m₂

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

interpPrim ∷ 𝕊 → 𝐿 Val → Val
interpPrim "LTE" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≤ i₂
interpPrim "LTE" (tohs → [ShareV (ValS (IntMV i₁) φ₁ ps₁),ShareV (ValS (IntMV i₂) φ₂ ps₂)]) 
  | (φ₁ ≡ φ₂) ⩓ (ps₁ ≡ ps₂) = ShareV $ ValS (BoolMV $ i₁ ≤ i₂) φ₁ ps₁
interpPrim "PLUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ + i₂
interpPrim s vs = pptrace s $ pptrace vs $ error "interpPrim: not implemented"

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
    restrictMode (SecM p) $ interpExp e
  ParE psA e → do
    let ps = pow $ map extract $ iter $ extract psA
    joins ^$ mapMOn (iter ps) $ \ p → do
      restrictMode (SecM p) $ interpExp e
  ShareE φA psA e → do
    let φ = extract φA
    let ps = pow $ map extract $ iter $ extract psA
    ṽ ← interpExp e
    return $ case ṽ of
      SecVP _p v → case v of
        BoolV b → AllVP $ ShareV $ ValS (BoolMV b) φ ps
        IntV i → AllVP $ ShareV $ ValS (IntMV i) φ ps
        _ → error "interpExp: ShareE: SecVP: v ∉ {BoolV _,IntV _}"
      _ → error "interpExp: ShareE: ṽ ≢ SecVP _ _"
  -- CirE e → do
  --   ṽ ← interpExp e
  --   return $ AllVP $ CircV $ case ṽ of
  --     SecVP p v → case v of
  --       BoolV b → BoolC (Some $ Inl p) b
  --       IntV i → IntC (Some $ Inl p) i
  --       _ → pptrace (annotatedTag eA) $ error "interpExp: CirE: SecVP: v ∉ {BoolV _,IntV _}"
  --     _ → pptrace (annotatedTag eA) $ pptrace ṽ $ error "interpExp: CirE: ṽ ≢ SecVP _ _"
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
  -- DelegateE
  -- MPCE φA psA e → do
  --   let φ = extract φA
  --   let ps = pow $ map extract $ iter $ extract psA
  --   ṽ ← interpExp e
  --   let v = case ṽ of
  --         AllVP v' → v'
  --         SSecVP ps' v'
  --           | ps ⊆ ps' → v'
  --           | otherwise → error "interpExp: MPCE: SSec: ps ⊈ ps'"
  --         _ → error "interpExp: MPCE: ṽ ∉ {AllVP _,SSec _ _}"
  --   return $ AllVP $ CircV $ case v of
  --     CircV c → case interpCirc c of
  --       Inl b → BoolC (Some $ Inr $ schemeProt φ) b
  --       Inr i → IntC (Some $ Inr $ schemeProt φ) i
  --     _ → error "interpExp: MPCE: v ≢ CircV _"
  RevealE psA e → do
    let ps = pow $ map extract $ iter $ extract psA
    ṽ ← interpExp e
    case ṽ of
      AllVP v → return $ SSecVP ps $ case v of
        (ShareV (ValS (BoolMV b) _ _)) → BoolV b
        (ShareV (ValS (IntMV i) _ _)) → IntV i
        _ → error "interpExp: RevealE: v ∉ {ShaveV (ValS (BoolMV _) _ _),ShareV (ValS (IntMV _) _ _)}"
      _ → error "interpExp: RevealE: ṽ ≢ AllVP _"
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
    -- bindValP ṽ₁ $ \ v₁ →
    --   bindValP ṽ₂ $ \ v₂ →
    --     return $ AllVP $ case (v₁,v₂) of
    --       (IntV i₁,IntV i₂) → case o of
    --         "LET" → BoolV $ i₁ ≤ i₂
    --         "PLUS" → IntV $ i₁ + i₂
    --         _ → error "interpExp: opperation not implemented"
    --       (CircV c₁,CircV c₂) → CircV $ OpC o $ list [c₁,c₂]
    --       (_,_) → error "interpExp: PrimE: not implemented, or bad prim application"
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
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"
