module PSL.Interpreter where

import UVMHS
import AddToUVMHS

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
  | NatMV IPrecision ℕ
  | IntMV IPrecision ℤ
  | FltMV FPrecision 𝔻
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
  | NatV IPrecision ℕ
  | IntV IPrecision ℤ
  | FltV FPrecision 𝔻
  | BulV
  | LV Val
  | RV Val
  | PairV Val Val
  | NilV
  | ConsV Val Val
  | CloV (𝑂 Var) Pat Exp ICloCxt
  | TCloV TVar Exp ICloCxt
  | ShareV ValS
  | PrinV Prin
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
  SecVP ρ₁ v₁ ⊔ SecVP ρ₂ v₂ | ρ₁ ≢ ρ₂ = ISecVP $ dict [ρ₁ ↦ v₁,ρ₂ ↦ v₂]
  -- SecVP ρ₁ v₁ ⊔ SecVP ρ₂ v₂ =
  --   if ρ₁ ≢ ρ₂ 
  --     then ISecVP $ dict [ρ₁ ↦ v₁,ρ₂ ↦ v₂]
  --     else <try next pattern>
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
  { iCloCxtEnv ∷ Env   -- γ = runtime environment
  , iCloCxtMode ∷ Mode -- m = executon mode (e.g., secure party A)
  } deriving (Eq,Ord,Show)

makePrettySum ''Val
makePrettySum ''ValP
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''ICloCxt
makeLenses ''ICloCxt

-- ξ̇ ∈ cxt
data ICxt = ICxt
  { iCxtSource ∷ 𝑂 FullContext -- the source location for the current expression being interpreted
  , iCxtClo ∷ ICloCxt          -- runtime context that should be captured by closures
  }
makeLenses ''ICxt 
-- this generates:
-- iCxtSourceL ∷ (ICxt ⟢ 𝑂 FullContext) -- this is a lens
-- iCxtClo ∷ ICxt ⟢ ICloCxt
-- to compose lenses, you can do `l₁ ⊚ l₂`

iCxtEnvL ∷ ICxt ⟢ Env
iCxtEnvL = iCloCxtEnvL ⊚ iCxtCloL

iCxtModeL ∷ ICxt ⟢ Mode
iCxtModeL = iCloCxtModeL ⊚ iCxtCloL

ξ₀ ∷ ICxt
ξ₀ = ICxt None $ ICloCxt dø TopM

------------
-- OUTPUT --
------------

data ResEv = ResEv
  { resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 Prin
  , resEvType ∷ Type
  , resEvOp ∷ 𝕊
  , resEvArgs ∷ 𝐿 Val
  } deriving (Eq,Ord,Show)
makePrettySum ''ResEv
makeLenses ''ResEv

data IOut = IOut
  { iOutResEvs ∷ 𝐼 ResEv
  } deriving (Show)
makePrettySum ''IOut
makeLenses ''IOut

instance Null IOut where null = IOut null
instance Append IOut where IOut res₁ ⧺ IOut res₂ = IOut $ res₁ ⧺ res₂
instance Monoid IOut

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
  , iErrorCallStack ∷ CallStack
  , iErrorClass ∷ IErrorClass
  , iErrorMsg ∷ Doc
  }

throwIErrorCxt ∷ (Monad m,MonadReader ICxt m,MonadError IError m,STACK) ⇒ IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIErrorCxt ec em vals = withFrozenCallStack $ do
  es ← askL iCxtSourceL
  throwIError es ec em vals
  
throwIError ∷ (Monad m,MonadError IError m,STACK) ⇒ 𝑂 FullContext → IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIError es ec em vals =
  throw $ IError es callStack ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n,ppString "=",v]
    ]

--------------
-- TL MONAD --
--------------

-- Interpreter, Top-Level Monad
newtype ITLM a = ITLM { unITLM ∷ RWST () IOut ITLState (ErrorT IError ID) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ()      -- operations: ask and local (local is slightly different from usual)
  , MonadWriter IOut    -- operations: tell and hijack (hijack is slightly different from usual)
  , MonadState ITLState -- operations: get and put
  , MonadError IError   -- operations: throw and catch
  )

mkITLM ∷ (ITLState → IError ∨ (ITLState ∧ IOut ∧ a)) → ITLM a
mkITLM f = ITLM $ mkRWST $ \ () σ → ErrorT $ ID $ f σ

runITLM ∷ ITLState → ITLM a → IError ∨ (ITLState ∧ IOut ∧ a)
runITLM σ xM = unID $ unErrorT $ runRWST () σ $ unITLM xM

evalITLM ∷ ITLState → ITLM a → IError ∨ a
evalITLM σ = map snd ∘ runITLM σ

evalITLMIO ∷ ITLState → ITLM a → IO a
evalITLMIO σ xM = case evalITLM σ xM of
  Inl (IError rsO cs rc rm) → do
    pprint $ ppVertical $ concat
      [ single𝐼 $ ppHeader $ show𝕊 rc
      , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
      , single𝐼 rm
      , single𝐼 $ pretty cs
      ]
    abortIO
  Inr x → return x

-----------
-- MONAD --
-----------

-- Interpreter Monad
newtype IM a = IM { unIM ∷ RWST ICxt IOut () (ErrorT IError ID) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ICxt -- if you do `ask`, you'll get a ICxt
  , MonadWriter IOut
  , MonadState ()
  , MonadError IError
  )

mkIM ∷ (ICxt → IError ∨ (IOut ∧ a)) → IM a
mkIM f = IM $ mkRWST $ \ γ () → ErrorT $ ID $ case f γ of
  Inl r → Inl r
  Inr (o :* x) → Inr $ () :* o :* x

runIM ∷ ICxt → IM a → IError ∨ (IOut ∧ a)
runIM γ xM = case unID $ unErrorT $ runRWST γ () $ unIM xM of
  Inl r → Inl r
  Inr (() :* o :* x) → Inr (o :* x)

asTLM ∷ IM a → ITLM a
asTLM xM = mkITLM $ \ σ → case runIM (update iCxtEnvL (itlStateEnv σ) ξ₀) xM of
  Inl r → Inl r
  Inr (o :* x) → Inr $ σ :* o :* x

-- =========== --
-- INTERPRETER --
-- =========== --

----------------
-- TRUNCATING --
----------------

trNat ∷ ℕ → ℕ → ℕ
trNat m n = n ÷ (2 ^^ m)

trPrNat ∷ IPrecision → ℕ → ℕ
trPrNat = \case
  InfIPr → id
  FixedIPr m n → trNat $ m + n

buNat ∷ ℕ → ℕ → ℕ
buNat m n = n + (2 ^^ m)

buPrNat ∷ IPrecision → ℕ → ℕ
buPrNat = \case
  InfIPr → id
  FixedIPr m n → buNat $ m + n

trInt ∷ ℕ → ℤ → ℤ
trInt m i
  | i < neg (int (2 ^^ (m - 1))) = trInt m (i + int (2 ^^ m))
  | i > int (2 ^^ (m - 1) - 1) = trInt m (i - int (2 ^^ m))
  | otherwise = i

trPrInt ∷ IPrecision → ℤ → ℤ
trPrInt = \case
  InfIPr → id
  FixedIPr m n → trInt $ m + n

----------------
-- PRIMITIVES --
----------------

interpPrimRaw ∷ 𝕊 → 𝐿 Val → IM Val
interpPrimRaw o vs = case (o,vs) of
  ("OR",tohs → [BoolV b₁,BoolV b₂]) → return $ BoolV $ b₁ ⩔ b₂
  ("AND",tohs → [BoolV b₁,BoolV b₂]) → return $ BoolV $ b₁ ⩓ b₂
  ("PLUS",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ n₁ + n₂
  ("PLUS",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ + i₂
  ("MINUS",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  ("MINUS",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ - i₂
  ("TIMES",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ n₁ × n₂
  ("TIMES",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ × i₂
  ("DIV",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0 then n₁ else n₁ ⌿ n₂
  ("DIV",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  ("MOD",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0 then n₁ else n₁ ÷ n₂
  ("MOD",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  ("EQ",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV $ n₁ ≡ n₂
  ("EQ",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV $ i₁ ≡ i₂
  ("LT",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV $ n₁ < n₂
  ("LT",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV $ i₁ < i₂
  ("GT",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV $ n₁ > n₂
  ("GT",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV $ i₁ > i₂
  ("LTE",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV $ n₁ ≤ n₂
  ("LTE",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV $ i₁ ≤ i₂
  ("GTE",tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV $ n₁ ≥ n₂
  ("GTE",tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV $ i₁ ≥ i₂
  ("COND",tohs → [BoolV b,v₁,v₂]) → return $ if b then v₁ else v₂
  _ → throwIErrorCxt NotImplementedIError "interpPrimRaw" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]

mpcFrVal ∷ Val → ValMPC
mpcFrVal (BoolV b) = BoolMV b
mpcFrVal (NatV pr n) = NatMV pr n
mpcFrVal (IntV pr i) = IntMV pr i
mpcFrVal (FltV pr i) = FltMV pr i
mpcFrVal _ = error "mpcFrVal"

valFrMPC ∷ ValMPC → Val
valFrMPC (BoolMV b) = BoolV b
valFrMPC (NatMV pr n) = NatV pr n
valFrMPC (IntMV pr i) = IntV pr i
valFrMPC (FltMV pr d) = FltV pr d

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
  ShareV (ValS φ' ρs' v) :& vs'' | (φ ≡ φ') ⩓ (ρs ≡ ρs') → 
    onRawShareVals φ ρs (vs ⧺ single (valFrMPC v)) f vs''
  _ → throwIErrorCxt TypeIError "onRawShareVals: vs' ∉ {Nil,ShareV …}" $ frhs
    [ ("vs'",pretty vs')
    , ("φ",pretty φ)
    , ("ρs",pretty ρs)
    ]

onRawVals ∷ 𝕊 → (𝐿 Val → IM Val) → 𝐿 Val → IM Val
onRawVals op f vs = case vs of
  ShareV (ValS φ ρs v) :& _ → do
    v' ← onRawShareVals φ ρs null f vs
    let τ = case v of
          BoolMV _ → 𝔹T
          NatMV pr _ → ℕT pr
          IntMV pr _ → ℤT pr
          FltMV pr _ → 𝔽T pr
    tellL iOutResEvsL $ single $ ResEv φ ρs τ op vs
    return v'
  _ → f vs

interpPrim ∷ 𝕊 → 𝐿 Val → IM Val
interpPrim op = onRawVals op $ interpPrimRaw op

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
bindVar x ṽ = mapEnvL iCxtEnvL ((x ↦ ṽ) ⩌)
-- bindVar x ṽ im = do
--   γ ← askL iCxtEnvL
--   let γ' = (x ↦ ṽ) ⩌ γ
--   localL iCxtEnvL γ' im


--------------
-- PATTERNS --
--------------

bindPat ∷ Pat → ValP → IM ValP → IM ValP
bindPat ψ ṽ vM = do
  fO ← bindPatO ψ ṽ
  case fO of
    Some f → f vM
    None → throwIErrorCxt TypeIError "bindPat: no matching cases" $ frhs
      [ ("ψ",pretty ψ)
      , ("ṽ",pretty ṽ)
      ]

bindPatO ∷ Pat → ValP → IM (𝑂 (IM a → IM a))
bindPatO ψ ṽ = case ψ of
  VarP x → return $ Some $ bindVar x ṽ
  BulP → return $ Some id
  NilP → do
    ṽ' ← bindValP ṽ $ \ v → case v of
          NilV → return $ AllVP $ NilV
          _ → return TopVP
    -- traceM "hi"
    -- pptraceM ṽ'
    return $ case ṽ' of
      TopVP → None
      _ → Some id
  ConsP ψ₁ ψ₂ → do
    ṽ₁ ← bindValP ṽ $ \ v → case v of
      ConsV v₁ _v₂ → return $ AllVP $ v₁
      _ → return TopVP
    ṽ₂ ← bindValP ṽ $ \ v → case v of
      ConsV _v₁ v₂ → return $ AllVP $ v₂
      _ → return TopVP
    fO₁ ← bindPatO ψ₁ ṽ₁
    fO₂ ← bindPatO ψ₂ ṽ₂
    return $ do
      f₁ ← fO₁
      f₂ ← fO₂
      return $ f₂ ∘ f₁
  TupP ψ₁ ψ₂ → do
    ṽ₁ ← bindValP ṽ $ \ v → case v of
      PairV v₁ _v₂ → return $ AllVP $ v₁
      _ → return TopVP
    ṽ₂ ← bindValP ṽ $ \ v → case v of
      PairV _v₁ v₂ → return $ AllVP $ v₂
      _ → return TopVP
    fO₁ ← bindPatO ψ₁ ṽ₁
    fO₂ ← bindPatO ψ₂ ṽ₂
    return $ do
      f₁ ← fO₁
      f₂ ← fO₂
      return $ f₂ ∘ f₁
  WildP → return $ Some id
  _ → return $ Some $ const $ throwIErrorCxt NotImplementedIError "bindPatO" $ frhs
    [ ("ψ",pretty ψ)
    , ("ṽ",pretty ṽ)
    ]

interpCase ∷ ValP → 𝐿 (Pat ∧ Exp) → IM ValP
interpCase v ψes = case ψes of
  Nil → throwIErrorCxt TypeIError "interpCase: ψes = []" $ frhs
    [ ("ψes",pretty ψes)
    ]
  (ψ :* e) :& ψes' → do
    fO ← bindPatO ψ v 
    case fO of
      None → interpCase v ψes'
      Some f → f $ interpExp e

--------------------
-- PARSING INPUTS --
--------------------

parseTy ∷ Type → 𝕊 → IM Val
parseTy τ s = case τ of
  ℤT pr → do
    let i = HS.read $ chars s ∷ ℤ
    return $ IntV pr $ trPrInt pr i
  ListT τ' → do
    vs ← mapM (parseTy τ') $ list $ filter (≢ "") $ splitOn𝕊 "\n" s
    return $ foldr NilV ConsV vs
  ℙT → do
    return $ PrinV $ var s
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
  BoolE b → return $ AllVP $ BoolV b
  StrE s → return $ AllVP $ StrV s
  NatE pr n → return $ AllVP $ NatV pr $ trPrNat pr n
  IntE pr i → return $ AllVP $ IntV pr $ trPrInt pr i
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
  NilE → return $ AllVP NilV
  ConsE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    bindValP ṽ₁ $ \ v₁ →
      bindValP ṽ₂ $ \ v₂ →
        return $ AllVP $ ConsV v₁ v₂
  LetTyE _ _ e' → interpExp e'
  LetE ψ e₁ e₂ → do
    v ← interpExp e₁
    bindPat ψ v $ interpExp e₂
  CaseE e' ψes → do
    ṽ ← interpExp e'
    interpCase ṽ ψes
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
        IntV pr i → return $ AllVP $ ShareV $ ValS φ pρs $ IntMV pr i
        _ → throwIErrorCxt TypeIError "interpExp: ShareE: AllVP: v ∉ {BoolV _,IntV _}" $ frhs
          [ ("v",pretty v)
          ]
      SecVP _p v → case v of
        BoolV b → return $ AllVP $ ShareV $ ValS φ pρs $ BoolMV b
        IntV pr i → return $ AllVP $ ShareV $ ValS φ pρs $ IntMV pr i
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
        ShareV (ValS _ _ (IntMV pr i)) → return $ IntV pr i
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

interpretFile ∷ 𝕊 → IO (IOut ∧ ITLState )
interpretFile fn = do
  s ← read fn
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  evalITLMIO σtl₀ $ do
    o ← retOut $ interpTLs tls
    σ ← get
    return $ o :* σ

interpretExample ∷ 𝕊 → IO ValP
interpretExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  o₁ :* σtl ← interpretFile path
  let v = itlStateEnv σtl ⋕! var "main"
  o₂ :* v' ← evalITLMIO σtl $ hijack $ asTLM $ interpApp v $ AllVP BulV
  write ("resources/" ⧺ fn ⧺ ".res") $ "RESOURCE ESTIMATION\n" ⧺ concat (inbetween "\n" $ map show𝕊 $ iOutResEvs $ o₁ ⧺ o₂)
  return v'

interpretTest ∷ 𝕊 → IO (ValP ∧ ValP)
interpretTest fn = do
  _ :* σtl ← interpretFile fn
  let v = itlStateEnv σtl ⋕! var "main"
      ev = itlStateEnv σtl ⋕! var "expected"
  v' ← evalITLMIO σtl $ asTLM $ interpApp v $ AllVP BulV
  return $ v' :* ev

testInterpreterExample ∷ 𝕊 → IO ()
testInterpreterExample fn = pprint *$ interpretExample fn

testInterpreter ∷ IO ()
testInterpreter = do
  pprint $ ppHeader "TESTING INTERPRETER"
  indir "tests" $ do
    fs ← files
    pprint $ ppVertical
      [ ppHeader "TESTS"
      , concat
        [ ppSpace $ 𝕟64 2
        , ppAlign $ ppVertical $ mapOn fs $ \ fn →
            let v :* ev = ioUNSAFE $ interpretTest fn
            in case v ≡ ev of
              True → ppHorizontal [ppFormat (formats [FG darkGreen]) $ ppString "PASSED",ppString fn]
              False → ppVertical
                [ ppHorizontal [ppFormat (formats [FG darkRed]) $ ppString "FAILED",ppString fn]
                , concat
                    [ ppSpace $ 𝕟64 2
                    , ppAlign $ ppVertical
                        [ ppHorizontal [ppHeader "RETURNED:",pretty v]
                        , ppHorizontal [ppHeader "EXPECTED:",pretty ev]
                        ]
                    ]
                ]
        ]
      ]
  testInterpreterExample "cmp"
  testInterpreterExample "cmp-tutorial"
  testInterpreterExample "euclid"
  testInterpreterExample "msort"
  -- testInterpreterExample "atqtest"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"
