module PSL.Interpreter where

import UVMHS
import PSL.Parser
import PSL.Syntax

import PSL.Data.Mode

import qualified Prelude as HS

-----------------
-- ENVIRONMENT --
-----------------

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
  | NatV ℕ
  | IntV ℤ
  | FltV 𝔻
  | BulV
  | LV Val
  | RV Val
  | PairV Val Val
  | NilV
  | ConsV Val Val
  | CloV (𝑂 Var) Pat Exp ICloCxt
  | TCloV TVar Exp ICloCxt
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
isecFrSSec ρs v = dict $ mapOn (iter ρs) $ \ ρ → ρ ↦ v

instance Bot ValP where bot = BotVP
instance Join ValP where
  BotVP ⊔ ṽ = ṽ
  ṽ ⊔ BotVP = ṽ
  SecVP ρ₁ v₁ ⊔ SecVP ρ₂ v₂ | ρ₁ ≢ ρ₂ = ISecVP $ dict $ [ρ₁ ↦ v₁,ρ₂ ↦ v₂]
  SecVP ρ₁ v₁ ⊔ ISecVP pvs₂ | ρ₁ ∉ keys pvs₂ = ISecVP $ (ρ₁ ↦ v₁) ⩌ pvs₂
  ISecVP pvs₁ ⊔ SecVP ρ₂ v₂ | ρ₂ ∉ keys pvs₁ = ISecVP $ (ρ₂ ↦ v₂) ⩌ pvs₁
  ISecVP pvs₁ ⊔ ISecVP pvs₂ | keys pvs₁ ∩ keys pvs₂ ≡ pø = ISecVP $ pvs₁ ⩌ pvs₂
  _ ⊔ _ = TopVP
instance JoinLattice ValP

-- γ ∈ ienv
type Env = 𝕏 ⇰ ValP

-----------
-- STATE --
-----------

-- σ ∈ itlstate
newtype ITLState = ITLState
  { itlStateEnv ∷ Env 
  } deriving (Eq,Ord,Show)

σtl₀ ∷ ITLState
σtl₀ = ITLState dø

-------------
-- CONTEXT --
-------------

-- ξ ∈ clo-cxt
data ICloCxt = ICloCxt
  { iCloCxtEnv ∷ Env
  , iCloCxtMode ∷ Mode
  } deriving (Eq,Ord,Show)

makePrettySum ''Val
makePrettySum ''ValP
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''ICloCxt
makeLenses ''ICloCxt

-- ξ̇ ∈ cxt
data ICxt = ICxt
  { iCxtSource ∷ 𝑂 FullContext
  , iCxtClo ∷ ICloCxt
  }
makeLenses ''ICxt

iCxtEnvL ∷ ICxt ⟢ Env
iCxtEnvL = iCloCxtEnvL ⊚ iCxtCloL

iCxtModeL ∷ ICxt ⟢ Mode
iCxtModeL = iCloCxtModeL ⊚ iCxtCloL

ξ₀ ∷ ICxt
ξ₀ = ICxt None $ ICloCxt dø TopM

-----------
-- ERROR --
-----------

data IErrorClass = 
    SyntaxIError 
  | TypeIError 
  | NotImplementedIError 
  | InternalIError
  deriving (Eq,Ord,Show)
makePrettySum ''IErrorClass

-- r ∈ cerr
data IError = IError
  { iErrorSource ∷ 𝑂 FullContext
  , iErrorClass ∷ IErrorClass
  , iErrorMsg ∷ Doc
  }

throwIErrorCxt ∷ (Monad m,MonadReader ICxt m,MonadError IError m) ⇒ IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIErrorCxt ec em vals = do
  es ← askL iCxtSourceL
  throwIError es ec em vals
  
throwIError ∷ (Monad m,MonadError IError m) ⇒ 𝑂 FullContext → IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIError es ec em vals =
  throw $ IError es ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n,ppString "=",v]
    ]

--------------
-- TL MONAD --
--------------

newtype ITLM a = ITLM { unITLM ∷ RWST () () ITLState (ErrorT IError ID) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ()
  , MonadWriter ()
  , MonadState ITLState
  , MonadError IError
  )

mkITLM ∷ (ITLState → IError ∨ (ITLState ∧ a)) → ITLM a
mkITLM f = ITLM $ mkRWST $ \ () σ → ErrorT $ ID $ case f σ of
  Inl r → Inl r
  Inr (σ' :* x) → Inr (σ' :* () :* x)

runITLM ∷ ITLState → ITLM a → IError ∨ (ITLState ∧ a)
runITLM σ xM = case unID $ unErrorT $ runRWST () σ $ unITLM xM of
  Inl r → Inl r
  Inr (σ' :* () :* x) → Inr (σ' :* x)

evalITLM ∷ ITLState → ITLM a → IError ∨ a
evalITLM σ = map snd ∘ runITLM σ

evalITLMIO ∷ ITLState → ITLM a → IO a
evalITLMIO σ xM = case evalITLM σ xM of
  Inl (IError rsO rc rm) → do
    pprint $ ppVertical
      [ ppHeader $ show𝕊 rc
      , elim𝑂 null pretty rsO
      , rm
      ]
    abortIO
  Inr x → return x

-----------
-- MONAD --
-----------

newtype IM a = IM { unIM ∷ RWST ICxt () () (ErrorT IError ID) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ICxt
  , MonadWriter ()
  , MonadState ()
  , MonadError IError
  )

mkIM ∷ (ICxt → IError ∨ a) → IM a
mkIM f = IM $ mkRWST $ \ γ () → ErrorT $ ID $ case f γ of
  Inl r → Inl r
  Inr x → Inr $ () :* () :* x

runIM ∷ ICxt → IM a → IError ∨ a
runIM γ xM = case unID $ unErrorT $ runRWST γ () $ unIM xM of
  Inl r → Inl r
  Inr (() :* () :* x) → Inr x

asTLM ∷ IM a → ITLM a
asTLM xM = mkITLM $ \ σ → case runIM (update iCxtEnvL (itlStateEnv σ) ξ₀) xM of
  Inl r → Inl r
  Inr x → Inr $ σ :* x

-- =========== --
-- INTERPRETER --
-- =========== --

----------------
-- PRIMITIVES --
----------------

interpPrimRaw ∷ 𝕊 → 𝐿 Val → Val
interpPrimRaw "OR" (tohs → [BoolV b₁,BoolV b₂]) = BoolV $ b₁ ⩔ b₂
interpPrimRaw "AND" (tohs → [BoolV b₁,BoolV b₂]) = BoolV $ b₁ ⩓ b₂
interpPrimRaw "PLUS" (tohs → [NatV n₁,NatV n₂]) = NatV $ n₁ + n₂
interpPrimRaw "PLUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ + i₂
interpPrimRaw "MINUS" (tohs → [NatV n₁,NatV n₂]) = NatV $ n₁ - n₂
interpPrimRaw "MINUS" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ - i₂
interpPrimRaw "TIMES" (tohs → [NatV n₁,NatV n₂]) = NatV $ n₁ × n₂
interpPrimRaw "TIMES" (tohs → [IntV i₁,IntV i₂]) = IntV $ i₁ × i₂
interpPrimRaw "DIV" (tohs → [NatV n₁,NatV n₂]) = NatV $ if n₂ ≡ 0 then n₁ else n₁ ⌿ n₂
interpPrimRaw "DIV" (tohs → [IntV i₁,IntV i₂]) = IntV $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
interpPrimRaw "MOD" (tohs → [NatV n₁,NatV n₂]) = NatV $ if n₂ ≡ 0 then n₁ else n₁ ÷ n₂
interpPrimRaw "MOD" (tohs → [IntV i₁,IntV i₂]) = IntV $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
interpPrimRaw "EQ" (tohs → [NatV n₁,NatV n₂]) = BoolV $ n₁ ≡ n₂
interpPrimRaw "EQ" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≡ i₂
interpPrimRaw "LT" (tohs → [NatV n₁,NatV n₂]) = BoolV $ n₁ < n₂
interpPrimRaw "LT" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ < i₂
interpPrimRaw "GT" (tohs → [NatV n₁,NatV n₂]) = BoolV $ n₁ > n₂
interpPrimRaw "GT" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ > i₂
interpPrimRaw "LTE" (tohs → [NatV n₁,NatV n₂]) = BoolV $ n₁ ≤ n₂
interpPrimRaw "LTE" (tohs → [IntV i₁,IntV i₂]) = BoolV $ i₁ ≤ i₂
interpPrimRaw "GTE" (tohs → [NatV n₁,NatV n₂]) = BoolV $ n₁ ≥ n₂
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
onRawShareVals φ ρs vs f = \case
  Nil → ShareV $ ValS (mpcFrVal $ f $ list vs) φ ρs
  ShareV (ValS v φ' ρs') :& vs' | (φ ≡ φ') ⩓ (ρs ≡ ρs') → onRawShareVals φ ρs (vs ⧺ single (valFrMPC v)) f vs'
  _ → error "error"

onRawVals ∷ (𝐿 Val → Val) → 𝐿 Val → Val
onRawVals f vs = case vs of
  ShareV (ValS _ φ ρs) :& _ → onRawShareVals φ ρs null f vs
  _ → f vs

interpPrim ∷ 𝕊 → 𝐿 Val → Val
interpPrim = onRawVals ∘ interpPrimRaw

---------------
-- VARIABLES --
---------------

interpVar ∷ Var → IM ValP
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → throwIErrorCxt SyntaxIError "interpVar: x ∉ γ" $ frhs
      [ ("x",pretty x)
      , ("γ",pretty γ)
      ]

bindVar ∷ Var → ValP → IM a → IM a
bindVar x v = mapEnvL iCxtEnvL ((x ↦ v) ⩌)

--------------
-- PATTERNS --
--------------

bindPat ∷ Pat → ValP → IM a → IM a
bindPat ψ v = case ψ of
  VarP x → bindVar x v
  BulP → id
  _ → const $ throwIErrorCxt NotImplementedIError "bindPat" $ frhs
    [ ("ψ",pretty ψ)
    , ("v",pretty v)
    ]

--------------------
-- PARSING INPUTS --
--------------------

parseTy ∷ Type → 𝕊 → Val
parseTy τ s = case τ of
  ℤT (Some (64 :* None)) → IntV $ int (HS.read $ chars s ∷ ℤ64)
  _ → error "parseTy: not implemented"

-----------
-- MODES --
-----------

restrictValP ∷ Mode → ValP → ValP
restrictValP m x̃ = case (m,x̃) of
  (TopM,_) → x̃
  (_,TopVP) → TopVP
  (BotM,_) → BotVP
  (_,BotVP) → BotVP
  (SecM ρ,AllVP v) → SecVP ρ v
  (SecM ρ,SecVP ρ' v) | ρ ≡ ρ' → SecVP ρ' v
  (SecM ρ,SSecVP ρs v) | ρ ∈ ρs → SecVP ρ v
  (SecM ρ,ISecVP pvs) | ρ ∈ keys pvs → SecVP ρ $ pvs ⋕! ρ
  (SSecM ρs,AllVP v) → SSecVP ρs v
  (SSecM ρs,SecVP ρ' v) | ρ' ∈ ρs → SecVP ρ' v
  (SSecM ρs,SSecVP ρs' v) → SSecVP (ρs ∩ ρs') v
  (SSecM ρs,ISecVP pvs) → ISecVP $ restrict ρs pvs
  (_,_) → BotVP

restrictMode ∷ Mode → IM ValP → IM ValP
restrictMode m xM = do
  m' ← askL iCxtModeL
  ṽ ← localL iCxtModeL (m ⊓ m') xM
  return $ restrictValP m ṽ

---------------------
-- PARALLEL VALUES --
---------------------

bindValP ∷ ValP → (Val → IM ValP) → IM ValP
bindValP ṽ f = case ṽ of
  BotVP → return BotVP
  AllVP v → f v
  SecVP ρ v → restrictMode (SecM ρ) $ f v
  SSecVP ρs v → restrictMode (SSecM ρs) $ f v
  ISecVP pvs → 
    joins ^$ mapMOn (iter pvs) $ \ (ρ :* v) →
      restrictMode (SecM ρ) $ f v
  TopVP → error "bindValP: ṽ = TopVP"

bindValsPR ∷ 𝐼 Val → 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
bindValsPR vs ṽs f = case ṽs of
  Nil → f $ list vs
  ṽ :& ṽs' → bindValP ṽ $ \ v → bindValsPR (vs ⧺ single v) ṽs' f

bindValsP ∷ 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
bindValsP = bindValsPR null

-----------------
-- APPLICATION --
-----------------

interpApp ∷ ValP → ValP → IM ValP
interpApp ṽ₁ ṽ₂ =
  bindValP ṽ₁ $ \ v₁ → case v₁ of
    CloV selfO ψ e ξ → do
      let selfγ = case selfO of
            None → id
            Some self → bindVar self ṽ₁
      compose [localL iCxtCloL ξ,bindPat ψ ṽ₂,selfγ ] $ interpExp e
    _ → error "interpExp: AppE: v₁ ≢ CloV _ _ _ _"

-----------------
-- EXPRESSIONS --
-----------------

interpExp ∷ Exp → IM ValP
interpExp eA = case extract eA of
  VarE x → interpVar x
  -- BoolE
  StrE s → return $ AllVP $ StrV s
  NatE n → return $ AllVP $ NatV n
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
    ξ ← askL iCxtCloL
    return $ AllVP $ CloV selfO ψ e ξ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  -- TLamE
  -- TAppE
  SoloE ρ e → do
    restrictMode (SecM ρ) $ interpExp e
  ParE ρs e → do
    joins ^$ mapMOn (iter ρs) $ \ ρ → do restrictMode (SecM ρ) $ interpExp e
  ShareE φ ρs e → do
    let pρs = pow ρs
    ṽ ← interpExp e
    return $ case ṽ of
      AllVP v → case v of
        BoolV b → AllVP $ ShareV $ ValS (BoolMV b) φ pρs
        IntV i → AllVP $ ShareV $ ValS (IntMV i) φ pρs
        _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: AllVP: v ∉ {BoolV _,IntV _}"
      SecVP _p v → case v of
        BoolV b → AllVP $ ShareV $ ValS (BoolMV b) φ pρs
        IntV i → AllVP $ ShareV $ ValS (IntMV i) φ pρs
        _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: SecVP: v ∉ {BoolV _,IntV _}"
      _ → pptrace (annotatedTag eA) $ error "interpExp: ShareE: ṽ ≢ SecVP _ _"
  AccessE e ρ → do
    ṽ ← interpExp e
    return $ case ṽ of
      ISecVP pvs → case pvs ⋕? ρ of
        Some v → SecVP ρ v
        _ → error "interpExp: AccessE: ISecVP: pvs ⋕? ρ ≢ Some v"
      _ → error "interpExp: AccessE: ṽ ≢ ISecVP _"
  BundleE ρes → do
    joins ^$ mapMOn (iter ρes) $ \ (ρ :* e) → do
      restrictMode (SecM ρ) $ interpExp e
  -- BundleUnionE
  RevealE ρs e → do
    let pρs = pow ρs
    ṽ ← interpExp e
    case ṽ of
      AllVP v → return $ SSecVP pρs $ case v of
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
          SecM ρ → AllVP $ parseTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name ρ ⧺ "/" ⧺ fn
          SSecM _ → error "cannot read in shared secret mode"
          BotM → error "cannot read in bot mode"
      _ → error "interpExp: ReadE: v ≢ StrV _"
  -- InferE
  -- HoleE
  PrimE o es → do
    ṽs ← mapM interpExp es
    bindValsP ṽs $ \ vs → return $ AllVP $ interpPrim o vs
  TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  _ → pptrace (annotatedTag eA) $ error "interpExp: not implemented"

---------------
-- TOP LEVEL --
---------------

interpTL ∷ TL → ITLM ()
interpTL tl = case extract tl of
  DeclTL _ _ → skip
  DefnTL x ψs e →  do
    let e' = buildLambda (annotatedTag tl) x ψs e
    v ← asTLM $ interpExp e'
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL _ → skip
  _ → pptrace (annotatedTag tl) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 TL → ITLM ()
interpTLs = eachWith interpTL

-------------
-- TESTING --
-------------

interpretExample ∷ 𝕊 → IO ValP
interpretExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  s ← read path
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  σtl ← evalITLMIO σtl₀ $ retState $ interpTLs tls
  let v = itlStateEnv σtl ⋕! var "main"
  evalITLMIO σtl $ asTLM $ interpApp v $ AllVP BulV

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
