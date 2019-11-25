module PSL.Interpreter where

import UVMHS
import PSL.Syntax
import PSL.Parser

import qualified Prelude as HS

data Val =
    IntV ℤ
  | NatV ℕ
  | StrV 𝕊
  | PairV Val Val
  | CloV (𝑂 𝕏) APat AExp IEnv
  | SoloV Prin Val
  | SSecV (𝑃 Prin) Val
  | ISecV (Prin ⇰ Val)
  | ReadTyV Type
  | ReadTyFnV Type 𝕊
  | ReturnV Val
  deriving (Eq,Ord,Show)

type Env = 𝕏 ⇰ Val

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

data Mode =
    TLM
  | SoloM Prin
  | SSecM (𝑃 Prin)
  | ISecM (𝑃 Prin)
  deriving (Eq,Ord,Show)

data IEnv = IEnv
  { iEnvEnv ∷ Env
  , iEnvMode ∷ Mode
  } deriving (Eq,Ord,Show)

ξ₀ ∷ IEnv
ξ₀ = IEnv dø TLM

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
asTLM xM = ITLM $ mkRWS $ \ () σ → let () :* () :* x = runRWS (ξ₀ { iEnvEnv = itlStateEnv σ }) () $ unIM xM in σ :* () :* x

makePrettySum ''Val
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''Mode
makePrettySum ''IEnv
makeLenses ''IEnv

bindVar ∷ 𝕏 → Val → IM a → IM a
bindVar x v = mapEnvL iEnvEnvL ((x ↦ v) ⩌)
-- bindVar x v xM = do
--   m ← askL iEnvModeL
--   case m of
--     TLM → mapEnvL iEnvEnvL (\ γ → (x ↦ None ↦ v) ▶ γ) xM
--     SoloM p → mapEnvL iEnvEnvL (\ γ → (x ↦ Some p ↦ v) ▶ γ) xM
--     SSecM ps → mapEnvL iEnvEnvL (\ γ → (foldr γ₀ (▶) $ mapOn (iter ps) $ \ p → x ↦ Some p ↦ v) ▶ γ) xM
--     ISecM ps → mapEnvL iEnvEnvL (\ γ → (foldr γ₀ (▶) $ mapOn (iter ps) $ \ p → x ↦ Some p ↦ v) ▶ γ) xM

bindPat ∷ APat → Val → IM a → IM a
bindPat ψA v = case extract ψA of
  VarP x → bindVar x v
  _ → pptrace (annotatedTag ψA) $ error "bindPat: not implemented"

checkReadTy ∷ AType → IM ()
checkReadTy τA = case extract τA of
  ℤT (Some (64 :* None)) → skip
  _ → error "checkReadTy: not implemented"

readTy ∷ Type → 𝕊 → Val
readTy τ₀ s = case τ₀ of
  ℤT (Some (64 :* None)) → IntV $ int $ (HS.read $ chars s ∷ ℤ64)
  _ → error "readTy: not implemented"

readTyFile ∷ Type → 𝕊 → IM Val
readTyFile τ fn = do
  m ← askL iEnvModeL
  return $ case m of
    TLM → readTy τ $ ioUNSAFE $ read $ "examples-data/" ⧺ fn
    SoloM p → readTy τ $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name p ⧺ "/" ⧺ fn
    SSecM _ → error "type error: cannot read in shared secret mode"
    ISecM ps → ISecV $ dict $ mapOn (iter ps) $ \ p →
      let v = readTy τ $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name p ⧺ "/" ⧺ fn
      in p ↦ v
  
appVal ∷ Val → Val → IM Val
appVal v₁ v₂ = case v₁ of
  ReadTyV τ → case v₂ of
    StrV s → return $ ReadTyFnV τ s
    _ → error "interpExp: ReadV: type error"
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
  _ → error "interpExp: type error"

appMPCVal ∷ Val → IM Val
appMPCVal v = case v of
  ReturnV v → return v
  ReadTyFnV τ s → readTyFile τ s
  SoloV p vMPC → do
    v ← localL iEnvModeL (SoloM p) $ appMPCVal vMPC
    return $ SoloV p v
  SSecV ps vMPC → do
    v ← localL iEnvModeL (SSecM ps) $ appMPCVal vMPC
    return $ SSecV ps v
  _ → pptrace v $ error "appMPCVal: not implemented"

interpExp ∷ AExp → IM Val
interpExp sA = case extract sA of
  StrE s → return $ StrV s
  LetTyE _ _ e → interpExp e
  LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  LamE selfO ψ e → do
    ξ ← ask
    return $ CloV selfO ψ e ξ
  AppE e₁ e₂ → do
    v₁ ← interpExp e₁
    v₂ ← interpExp e₂
    appVal v₁ v₂
  BindE ψ e₁ e₂ → do
    vMPC ← interpExp e₁
    v ← appMPCVal vMPC
    bindPat ψ v $ interpExp e₂
  SoloE pA e → do
    v ← localL iEnvModeL (SoloM $ extract pA) $ interpExp e
    return $ SoloV (extract pA) v
  ReadE τA → do
    checkReadTy τA
    return $ ReadTyV $ extract τA
  _ → pptrace (annotatedTag sA) $ error "interpExp: not implemented"

interpTL ∷ ATL → ITLM ()
interpTL sA = case extract sA of
  DeclTL _ _ → skip
  DefnTL x e → do
    v ← asTLM $ interpExp e
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL _ → skip
  _ → pptrace (annotatedTag sA) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 ATL → ITLM ()
interpTLs = eachWith interpTL

testInterpreterExample ∷ 𝕊 → IO ()
testInterpreterExample fn = do
  s ← read $ "examples/" ⧺ fn ⧺ ".psl"
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  out $ "DONE PARSING:" ⧺ fn
  -- eachOn tls $ \ tl → pprint $ annotatedElem tl
  let σtl = evalITLM σtl₀ $ retState $ interpTLs tls
  pprint σtl

testInterpreter ∷ IO ()
testInterpreter = do
  testInterpreterExample "e1"
