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
  { sharedValProt ∷ Prot
  , sharedValPrins ∷ 𝑃 Prin
  , sharedValRaw ∷ ValMPC
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
  SecVP ρ₁ v₁ ⊔ ISecVP ρvs₂ | ρ₁ ∉ keys ρvs₂ = ISecVP $ (ρ₁ ↦ v₁) ⩌ ρvs₂
  ISecVP ρvs₁ ⊔ SecVP ρ₂ v₂ | ρ₂ ∉ keys ρvs₁ = ISecVP $ (ρ₂ ↦ v₂) ⩌ ρvs₁
  ISecVP ρvs₁ ⊔ ISecVP ρvs₂ | keys ρvs₁ ∩ keys ρvs₂ ≡ pø = ISecVP $ ρvs₁ ⩌ ρvs₂
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

interpPrimRaw ∷ 𝕊 → 𝐿 Val → IM Val
interpPrimRaw o vs = case (o,vs) of
  ("OR",tohs → [BoolV b₁,BoolV b₂]) → return $ BoolV $ b₁ ⩔ b₂
  ("AND",tohs → [BoolV b₁,BoolV b₂]) → return $ BoolV $ b₁ ⩓ b₂
  ("PLUS",tohs → [NatV n₁,NatV n₂]) → return $ NatV $ n₁ + n₂
  ("PLUS",tohs → [IntV i₁,IntV i₂]) → return $ IntV $ i₁ + i₂
  ("MINUS",tohs → [NatV n₁,NatV n₂]) → return $ NatV $ n₁ - n₂
  ("MINUS",tohs → [IntV i₁,IntV i₂]) → return $ IntV $ i₁ - i₂
  ("TIMES",tohs → [NatV n₁,NatV n₂]) → return $ NatV $ n₁ × n₂
  ("TIMES",tohs → [IntV i₁,IntV i₂]) → return $ IntV $ i₁ × i₂
  ("DIV",tohs → [NatV n₁,NatV n₂]) → return $ NatV $ if n₂ ≡ 0 then n₁ else n₁ ⌿ n₂
  ("DIV",tohs → [IntV i₁,IntV i₂]) → return $ IntV $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  ("MOD",tohs → [NatV n₁,NatV n₂]) → return $ NatV $ if n₂ ≡ 0 then n₁ else n₁ ÷ n₂
  ("MOD",tohs → [IntV i₁,IntV i₂]) → return $ IntV $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  ("EQ",tohs → [NatV n₁,NatV n₂]) → return $ BoolV $ n₁ ≡ n₂
  ("EQ",tohs → [IntV i₁,IntV i₂]) → return $ BoolV $ i₁ ≡ i₂
  ("LT",tohs → [NatV n₁,NatV n₂]) → return $ BoolV $ n₁ < n₂
  ("LT",tohs → [IntV i₁,IntV i₂]) → return $ BoolV $ i₁ < i₂
  ("GT",tohs → [NatV n₁,NatV n₂]) → return $ BoolV $ n₁ > n₂
  ("GT",tohs → [IntV i₁,IntV i₂]) → return $ BoolV $ i₁ > i₂
  ("LTE",tohs → [NatV n₁,NatV n₂]) → return $ BoolV $ n₁ ≤ n₂
  ("LTE",tohs → [IntV i₁,IntV i₂]) → return $ BoolV $ i₁ ≤ i₂
  ("GTE",tohs → [NatV n₁,NatV n₂]) → return $ BoolV $ n₁ ≥ n₂
  ("GTE",tohs → [IntV i₁,IntV i₂]) → return $ BoolV $ i₁ ≥ i₂
  ("COND",tohs → [BoolV b,v₁,v₂]) → return $ if b then v₁ else v₂
  _ → throwIErrorCxt NotImplementedIError "interpPrimRaw" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]

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

onRawShareVals ∷ Prot → 𝑃 Prin → 𝐼 Val → (𝐿 Val → IM Val) → 𝐿 Val → IM Val
onRawShareVals φ ρs vs f vs' = case vs' of
  Nil → ShareV ∘ ValS φ ρs ∘ mpcFrVal ^$ f $ list vs
  ShareV (ValS φ' ρs' v) :& vs'' | (φ ≡ φ') ⩓ (ρs ≡ ρs') → onRawShareVals φ ρs (vs ⧺ single (valFrMPC v)) f vs''
  _ → throwIErrorCxt TypeIError "onRawShareVals: vs' ∉ {Nil,ShareV …}" $ frhs
    [ ("vs'",pretty vs')
    , ("φ",pretty φ)
    , ("ρs",pretty ρs)
    ]

onRawVals ∷ (𝐿 Val → IM Val) → 𝐿 Val → IM Val
onRawVals f vs = case vs of
  ShareV (ValS φ ρs _) :& _ → onRawShareVals φ ρs null f vs
  _ → f vs

interpPrim ∷ 𝕊 → 𝐿 Val → IM Val
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

parseTy ∷ Type → 𝕊 → IM Val
parseTy τ s = case τ of
  ℤT (Some (64 :* None)) → return $ IntV $ int (HS.read $ chars s ∷ ℤ64)
  _ → throwIErrorCxt NotImplementedIError "parseTy" $ frhs
    [ ("τ",pretty τ)
    ]

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
  (SecM ρ,ISecVP ρvs) | ρ ∈ keys ρvs → SecVP ρ $ ρvs ⋕! ρ
  (SSecM ρs,AllVP v) → SSecVP ρs v
  (SSecM ρs,SecVP ρ' v) | ρ' ∈ ρs → SecVP ρ' v
  (SSecM ρs,SSecVP ρs' v) → SSecVP (ρs ∩ ρs') v
  (SSecM ρs,ISecVP ρvs) → ISecVP $ restrict ρs ρvs
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
  ISecVP ρvs → 
    joins ^$ mapMOn (iter ρvs) $ \ (ρ :* v) →
      restrictMode (SecM ρ) $ f v
  TopVP → throwIErrorCxt TypeIError "bindValP: ṽ = TopVP" $ frhs
    [ ("ṽ",pretty ṽ)
    ]

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
    _ → throwIErrorCxt TypeIError "interpExp: AppE: v₁ ≢ CloV _ _ _ _" $ frhs
      [ ("v₁",pretty v₁)
      ]

-----------------
-- EXPRESSIONS --
-----------------

interpExp ∷ Exp → IM ValP
interpExp e = localL iCxtSourceL (Some $ annotatedTag e) $ case extract e of
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
        _ → throwIErrorCxt TypeIError "interpExp: IfE: v ≢ BoolV _" $ frhs
          [ ("v",pretty v)
          ]
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
  LetTyE _ _ e' → interpExp e'
  LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  -- CaseE
  LamE selfO ψ e' → do
    ξ ← askL iCxtCloL
    return $ AllVP $ CloV selfO ψ e' ξ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  -- TLamE
  -- TAppE
  SoloE ρ e' → do
    restrictMode (SecM ρ) $ interpExp e'
  ParE ρs e' → do
    joins ^$ mapMOn (iter ρs) $ \ ρ → do restrictMode (SecM ρ) $ interpExp e'
  ShareE φ ρs e' → do
    let pρs = pow ρs
    ṽ ← interpExp e'
    case ṽ of
      AllVP v → case v of
        BoolV b → return $ AllVP $ ShareV $ ValS φ pρs $ BoolMV b
        IntV i → return $ AllVP $ ShareV $ ValS φ pρs $ IntMV i
        _ → throwIErrorCxt TypeIError "interpExp: ShareE: AllVP: v ∉ {BoolV _,IntV _}" $ frhs
          [ ("v",pretty v)
          ]
      SecVP _p v → case v of
        BoolV b → return $ AllVP $ ShareV $ ValS φ pρs $ BoolMV b
        IntV i → return $ AllVP $ ShareV $ ValS φ pρs $ IntMV i
        _ → throwIErrorCxt TypeIError "interpExp: ShareE: SecVP: v ∉ {BoolV _,IntV _}" $ frhs
          [ ("v",pretty v)
          ]
      _ → throwIErrorCxt TypeIError "interpExp: ShareE: ṽ ≢ SecVP _ _" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  AccessE e' ρ → do
    ṽ ← interpExp e'
    case ṽ of
      ISecVP ρvs → case ρvs ⋕? ρ of
        Some v → return $ SecVP ρ v
        _ → throwIErrorCxt TypeIError "interpExp: AccessE: ISecVP: ρvs ⋕? ρ ≢ Some _" $ frhs
          [ ("ρvs",pretty ρvs)
          , ("ρ",pretty ρ)
          ]
      _ → throwIErrorCxt TypeIError "interpExp: AccessE: ṽ ≢ ISecVP _" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  BundleE ρes → do
    joins ^$ mapMOn (iter ρes) $ \ (ρ :* e') → do
      restrictMode (SecM ρ) $ interpExp e'
  -- BundleUnionE
  RevealE ρs e' → do
    let pρs = pow ρs
    ṽ ← interpExp e'
    case ṽ of
      AllVP v → SSecVP pρs ^$ case v of
        ShareV (ValS _ _ (BoolMV b)) → return $ BoolV b
        ShareV (ValS _ _ (IntMV i)) → return $ IntV i
        _ → throwIErrorCxt TypeIError "interpExp: RevealE: v ∉ {ShaveV (ValS (BoolMV _) _ _),ShareV (ValS (IntMV _) _ _)}" $ frhs
          [ ("v",pretty v)
          ]
      _ → throwIErrorCxt TypeIError "interpExp: RevealE: ṽ ≢ AllVP _" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  -- AscrE
  ReadE τA e' → do
    ṽ ← interpExp e'
    bindValP ṽ $ \ v → case v of
      StrV fn → do
        m ← askL iCxtModeL
        case m of
          TopM → throwIErrorCxt TypeIError "cannot read at top level, must be in solo or par mode" null
          SecM ρ → AllVP ^$ parseTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ 𝕩name ρ ⧺ "/" ⧺ fn
          SSecM _ → throwIErrorCxt TypeIError "cannot read in shared secret mode" null
          BotM → throwIErrorCxt TypeIError "cannot read in bot mode" null
      _ → throwIErrorCxt TypeIError "interpExp: ReadE: v ≢ StrV _" $ frhs
        [ ("v",pretty v)
        ]
  -- InferE
  -- HoleE
  PrimE o es → do
    ṽs ← mapM interpExp es
    bindValsP ṽs $ \ vs → AllVP ^$ interpPrim o vs
  TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  _ → throwIErrorCxt NotImplementedIError "interpExp" null

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
