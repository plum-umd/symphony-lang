module PSL.Interpreter where

import UVMHS
import PSL.Syntax
import PSL.Parser

import qualified Prelude as HS

data Circ =
    BoolC (𝑂 Prin) 𝔹
  | IntC (𝑂 Prin) ℤ
  | OpC 𝕊 (𝐿 Circ)
  deriving (Eq,Ord,Show)
makePrettySum ''Circ

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
  | CloV (𝑂 AVar) APat AExp IEnv
  | TCloV 𝕏 AExp IEnv
  | CircV Circ
  | ParV (Prin ⇰ Val)
  deriving (Eq,Ord,Show)

data ValP =
    AllVP Val
  | SSecVP Val (𝑃 Prin)
  | ISecVP Val (Prin ⇰ Val)
  deriving (Eq,Ord,Show)

type Env = 𝕏 ⇰ ValP

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

data IEnv = IEnv
  { iEnvEnv ∷ Env
  , iEnvMode ∷ 𝑂 Prin
  } deriving (Eq,Ord,Show)

ξ₀ ∷ IEnv
ξ₀ = IEnv dø None

newtype IM a = IM { unIM ∷ RWS IEnv () () a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader IEnv
  ,MonadWriter ()
  ,MonadState ()
  )

mkIM ∷ (IEnv → a) → IM a
mkIM f = IM $ mkRWS $ \ γ () →
  let x = f γ
  in () :* () :* x

runIM ∷ IEnv → IM a → a
runIM γ xM =
  let () :* () :* x = runRWS γ () $ unIM xM
  in x

asTLM ∷ IM a → ITLM a
asTLM xM = ITLM $ mkRWS $ \ () σ → 
  let () :* () :* x = runRWS (ξ₀ { iEnvEnv = itlStateEnv σ }) () $ unIM xM 
  in σ :* () :* x

makePrettySum ''Val
makePrettySum ''ValP
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''IEnv
makeLenses ''IEnv

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

bindPat ∷ APat → ValP → IM a → IM a
bindPat ψA v = case extract ψA of
  VarP xA → do
    let x = extract xA
    mapEnvL iEnvEnvL ((x ↦ v) ⩌)
  BulP → id
  _ → pptrace (annotatedTag ψA) $ error "bindPat: not implemented"

parseTy ∷ AType → 𝕊 → Val
parseTy τA s = case extract τA of
  ℤT (Some (64 :* None)) → IntV $ int (HS.read $ chars s ∷ ℤ64)
  _ → error "parseTy: not implemented"

-- interpVarRaw ∷ AVar → IM (Val ∨ (Prin ⇰ Val))
-- interpVarRaw xA = do
--   let x = extract xA
--   γ ← askL iEnvEnvL
--   case γ ⋕? x of
--     Some ṽ → return ṽ
--     None → error "interpVarRaw: not in scope"
--     
-- interpVar ∷ AVar → IM Val
-- interpVar x = do
--   ṽ ← interpVarRaw x
--   m ← askL iEnvModeL
--   case (m,ṽ) of
--     (_,Inl v) → return v
--     (Some p,Inr pvs) 
--       | p ∈ keys pvs → return $ pvs ⋕! p
--       | otherwise → error "interpExp: VarE: p ∉ dom pvs"
--     (None,Inr pvs) → return $ ParV pvs

interpExp ∷ AExp → IM Val
interpExp eA = case extract eA of
  VarE x → interpVar x
  -- BoolE
  StrE s → return $ StrV s
  -- IntE
  -- FltE
  BulE → return $ BulV
  -- IfE
  -- LE
  -- RE
  -- TupE
  -- NilE
  -- ConsE
  LetTyE _ _ e → interpExp e
  LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  -- CaseE
  LamE selfO ψ e → do
    ξ ← ask
    return $ CloV selfO ψ e ξ
  AppE e₁ e₂ → do
    v₁ ← interpExp e₁
    v₂ ← interpExp e₂
    case v₁ of
      CloV selfO ψ e ξ → do
        let selfγ = case selfO of
              None → id
              Some self → bindVar self v₁
        compose
          [ local ξ 
          , bindPat ψ v₂
          , selfγ
          ] $
          interpExp e
      _ → pptrace (annotatedTag eA) $ error "interpExp: AppE: v₁ ≢ CloV _ _ _ _"
  -- TLamE
  -- TAppE
  ParE psA e → do
    let ps = pow $ map extract $ iter $ extract psA
    m ← askL iEnvModeL
    when (m ≢ None) $ \ _ → error "interpExp: ParE: m ≢ None"
    pvs ← dict ^$ mapMOn (iter ps) $ \ p → do
      v ← localL iEnvModeL (Some p) $ interpExp e
      return $ p ↦ v
    return $ ParV pvs
  CirE hA → case extract hA of
    VarPt x → do
      ṽ ← interpVarRaw x
      return $ CircV $ case ṽ of
        Inl v → case v of
          BoolV b → BoolC b
          IntV i → IntC i
          _ → error "interpExp: CirE: VarPt: Inl: v ∉ {BoolV _,IntV _}"
        _ → error "interpExp: CirE: VarPt: ṽ ≢ Inl _"
    AccessPt x pA → do
      let p = extract pA
      ṽ ← interpVarRaw x
      case ṽ of
        Inr pvs → case pvs ⋕? p of
          Some v' → return $ CircV $ case v' of
            BoolV b → BoolC b
            IntV i → IntC i
            _ → error "interpExp: AccessPt: ParV: Some: v' ≢ IntV _"
          _ → error "interpExp: AccessPt: ParV: pvs ⋕? p ≢ Some _"
        _ → error "interpExp: AccessPt: ṽ ≢ Inr _"
  BundleE pes → do
    pvs ← dict ^$ mapMOn (iter pes) $ \ (pA :* e) → do
      let p = extract pA
      v ← localL iEnvModeL (Some p) $ interpExp e
      return $ p ↦ v
    return $ ParV pvs
  -- BundleUnionE
  -- DelegateE
  MPCE _φ _ps e → do
    v ← interpExp e
    return $ CircV $ case v of
      CircV c → case interpCirc c of
        Inl b → BoolC b
        Inr i → IntC i
      _ → error "interpExp: MPCE: v ≢ CircV _"
  RevealE _ e → do
    v ← interpExp e
    return $ case v of
      CircV (BoolC b) → BoolV b
      CircV (IntC i) → IntV i
      _ → error "interpExp: RevealE: v ∉ {BoolC _,IntC i}"
  -- AscrE
  ReadE τA e → do
    v ← interpExp e
    case v of
      StrV fn → do
        m ← askL iEnvModeL
        return $ case m of
          None → readTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ fn
          Some p → readTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name p ⧺ "/" ⧺ fn
      _ → error "interpExp: ReadE: v ≢ StrV _"
  -- InferE
  -- HoleE
  PrimE "LTE" (tohs → [e₁,e₂]) → do
    v₁ ← interpExp e₁
    v₂ ← interpExp e₂
    return $ case (v₁,v₂) of
      (IntV i₁,IntV i₂) → IntV $ i₁ + i₂
      (CircV c₁,CircV c₂) → CircV $ OpC "LTE" $ list [c₁,c₂]
      (_,_) → error "interpExp: PrimE: not implemented, or bad prim application"
  _ → pptrace (annotatedTag eA) $ error "not implemented: interpExp"

interpTL ∷ ATL → ITLM ()
interpTL sA = case extract sA of
  DeclTL _ _ → skip
  DefnTL xA e → do
    let x = extract xA
    v ← asTLM $ interpExp e
    modifyL itlStateEnvL ((x ↦ Inl v) ⩌)
  PrinTL _ → skip
  _ → pptrace (annotatedTag sA) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 ATL → ITLM ()
interpTLs = eachWith interpTL

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
  testInterpreterExample "plus"
