module PSL.Interpreter where

import UVMHS
import AddToUVMHS

import PSL.Parser
import PSL.Syntax

import PSL.Data.Mode

import qualified Prelude as HS
import qualified Text.Read as HS

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

-- -- sv ∈ shared-val
-- data ValS = ValS
--   { sharedValProt ∷ Prot
--   , sharedValPrins ∷ 𝑃 PrinVal
--   , sharedValRaw ∷ ValMPC
--   } deriving (Eq,Ord,Show)

-- v ∈ val
data Val =
    BoolV 𝔹
  | StrV 𝕊
  | NatV IPrecision ℕ
  | IntV IPrecision ℤ
  | FltV FPrecision 𝔻
  | BulV
  | LV ValP
  | RV ValP
  | PairV ValP ValP
  | NilV
  | ConsV ValP ValP
  | CloV (𝑂 Var) Pat Exp ICloCxt
  | TCloV TVar Exp ICloCxt
  -- | ShareV ValS
  | PrinV PrinExpVal
  deriving (Eq,Ord,Show)

-- ṽ ∈ par-val
data ValP =
    BotVP
  | SSecVP (𝑃 PrinVal) Val
  | ISecVP (PrinVal ⇰ Val)
  | ShareVP Prot (𝑃 PrinVal) ValMPC
  | AllVP Val
  deriving (Eq,Ord,Show)

-- isecFrSSec ∷ 𝑃 PrinExp → Val → PrinExp ⇰ Val
-- isecFrSSec ρs v = dict $ mapOn (iter ρs) $ \ ρ → ρ ↦ v
-- 
-- instance Bot ValP where bot = BotVP
-- instance Join ValP where
--   BotVP ⊔ ṽ = ṽ
--   ṽ ⊔ BotVP = ṽ
--   SecVP ρ₁ v₁ ⊔ SecVP ρ₂ v₂ | ρ₁ ≢ ρ₂ = ISecVP $ dict [ρ₁ ↦ v₁,ρ₂ ↦ v₂]
--   -- SecVP ρ₁ v₁ ⊔ SecVP ρ₂ v₂ =
--   --   if ρ₁ ≢ ρ₂ 
--   --     then ISecVP $ dict [ρ₁ ↦ v₁,ρ₂ ↦ v₂]
--   --     else <try next pattern>
--   SecVP ρ₁ v₁ ⊔ ISecVP ρvs₂ | ρ₁ ∉ keys ρvs₂ = ISecVP $ (ρ₁ ↦ v₁) ⩌ ρvs₂
--   ISecVP ρvs₁ ⊔ SecVP ρ₂ v₂ | ρ₂ ∉ keys ρvs₁ = ISecVP $ (ρ₂ ↦ v₂) ⩌ ρvs₁
--   ISecVP ρvs₁ ⊔ ISecVP ρvs₂ | keys ρvs₁ ∩ keys ρvs₂ ≡ pø = ISecVP $ ρvs₁ ⩌ ρvs₂
--   _ ⊔ _ = AllVP
-- instance JoinLattice ValP

-- γ ∈ ienv
type Env = 𝕏 ⇰ ValP

-----------
-- STATE --
-----------

-- σ ∈ itlstate
data ITLState = ITLState
  { itlStateEnv ∷ Env
  , itlStateDeclPrins ∷ Prin ⇰ PrinKind
  } deriving (Eq,Ord,Show)

σtl₀ ∷ ITLState
σtl₀ = ITLState dø dø

-------------
-- CONTEXT --
-------------

-- ξ ∈ clo-cxt
data ICloCxt = ICloCxt
  { iCloCxtEnv ∷ Env   -- γ = runtime environment
  , iCloCxtMode ∷ Mode -- m = executon mode (e.g., secure party A)
  } deriving (Eq,Ord,Show)

makePrettySum ''Val
-- makePrettySum ''ValS
makePrettySum ''ValP
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''ICloCxt
makeLenses ''ICloCxt

-- ξ̇ ∈ cxt
data ICxt = ICxt
  { iCxtSource ∷ 𝑂 FullContext      -- the source location for the current expression being interpreted
  , iCxtClo ∷ ICloCxt               -- runtime context that should be captured by closures
  , iCxtDeclPrins ∷ Prin ⇰ PrinKind -- declared principles and their kinds
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
ξ₀ = ICxt None (ICloCxt dø TopM) dø

------------
-- OUTPUT --
------------

data ResEv = ResEv
  { resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 PrinVal
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
asTLM xM = mkITLM $ \ σ → 
  let ξ = update iCxtEnvL (itlStateEnv σ) $
          update iCxtDeclPrinsL (itlStateDeclPrins σ) $
          ξ₀
  in case runIM ξ xM of
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

mpcFrVal ∷ Val → IM ValMPC
mpcFrVal v = case v of
  BoolV b → return $ BoolMV b
  NatV pr n → return $ NatMV pr n
  IntV pr i → return $ IntMV pr i
  FltV pr i → return $ FltMV pr i
  _ → throwIErrorCxt TypeIError "mpcFrVal: cannot share value" $ frhs
    [ ("v",pretty v)
    ]

valFrMPC ∷ ValMPC → Val
valFrMPC = \case
  BoolMV b → BoolV b
  NatMV pr n → NatV pr n
  IntMV pr i → IntV pr i
  FltMV pr d → FltV pr d

-- rawShareOps ∷ 𝑃 𝕊
-- rawShareOps = pow
--   [ "LT"
--   , "GT"
--   , "LTE"
--   , "GTE"
--   , "PLUS"
--   , "MINUS"
--   , "TIMES"
--   , "DIV"
--   , "MOD"
--   , "EQ"
--   ]

-- onRawShareVals ∷ Prot → 𝑃 PrinVal → 𝐼 Val → (𝐿 Val → IM Val) → 𝐿 Val → IM Val
-- onRawShareVals φ ρs vs f vs' = case vs' of
--   Nil → ShareV ∘ ValS φ ρs ∘ mpcFrVal ^$ f $ list vs
--   ShareV (ValS φ' ρs' v) :& vs'' | (φ ≡ φ') ⩓ (ρs ≡ ρs') → 
--     onRawShareVals φ ρs (vs ⧺ single (valFrMPC v)) f vs''
--   _ → throwIErrorCxt TypeIError "onRawShareVals: vs' ∉ {Nil,ShareV …}" $ frhs
--     [ ("vs'",pretty vs')
--     , ("φ",pretty φ)
--     , ("ρs",pretty ρs)
--     ]
-- 
-- onRawVals ∷ 𝕊 → (𝐿 Val → IM Val) → 𝐿 Val → IM Val
-- onRawVals op f vs = case vs of
--   ShareV (ValS φ ρs v) :& _ → do
--     v' ← onRawShareVals φ ρs null f vs
--     let τ = case v of
--           BoolMV _ → 𝔹T
--           NatMV pr _ → ℕT pr
--           IntMV pr _ → ℤT pr
--           FltMV pr _ → 𝔽T pr
--     tellL iOutResEvsL $ single $ ResEv φ ρs τ op vs
--     return v'
--   _ → f vs
-- 
-- interpPrim ∷ 𝕊 → 𝐿 Val → IM Val
-- interpPrim op = onRawVals op $ interpPrimRaw op

---------------
-- VARIABLES --
---------------

interpVar ∷ Var → IM ValP
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → throwIErrorCxt SyntaxIError "interpVar: x ∉ dom(γ)" $ frhs
      [ ("x",pretty x)
      , ("dom(γ)",pretty $ keys γ)
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

bindPat ∷ Pat → ValP → IM a → IM a
bindPat ψ ṽ xM = do
  fO ← unFailT $ bindPatO ψ ṽ
  case fO of
    Some f → f xM
    None → throwIErrorCxt TypeIError "bindPat: no matching cases" $ frhs
      [ ("ψ",pretty ψ)
      , ("ṽ",pretty ṽ)
      ]

bindPatO ∷ Pat → ValP → FailT IM (IM a → IM a)
bindPatO ψ ṽ = case ψ of
  VarP x → return $ bindVar x ṽ
  BulP → return id
  NilP → do
    v ← inFailT $ elimValP ṽ
    case v of
      NilV → return id
      _ → abort
  ConsP ψ₁ ψ₂ → do
    v ← inFailT $ elimValP ṽ
    case v of
      ConsV ṽ₁ ṽ₂ → do
        f₁ ← bindPatO ψ₁ ṽ₁ 
        f₂ ← bindPatO ψ₂ ṽ₂
        return $ f₂ ∘ f₁
      _ → abort
  TupP ψ₁ ψ₂ → do
    v ← inFailT $ elimValP ṽ
    case v of
      PairV ṽ₁ ṽ₂ → do
        f₁ ← bindPatO ψ₁ ṽ₁ 
        f₂ ← bindPatO ψ₂ ṽ₂
        return $ f₂ ∘ f₁
      _ → abort
  WildP → return id
  _ → abort

interpCase ∷ ValP → 𝐿 (Pat ∧ Exp) → IM ValP
interpCase ṽ ψes = do
  fO ← unFailT $ interpCaseO ṽ ψes
  case fO of
    None → throwIErrorCxt TypeIError "interpCase: interpCaseO v ψes = None" $ frhs
      [ ("ṽ",pretty ṽ)
      , ("ψes",pretty ψes)
      ]
    Some ṽ' → return ṽ'

interpCaseO ∷ ValP → 𝐿 (Pat ∧ Exp) → FailT IM ValP
interpCaseO ṽ ψes = case ψes of
  Nil → abort
  (ψ :* e) :& ψes' → tries
    [ do f ← bindPatO ψ ṽ 
         inFailT $ f $ interpExp e
    , interpCaseO ṽ ψes'
    ]

--------------------
-- PARSING INPUTS --
--------------------

-- prinDataPath ∷ PrinExp → 𝕊
-- prinDataPath = \case
--   VarPE s → s
--   AccessPE s n → s ⧺ "_" ⧺ show𝕊 n

parseTy ∷ Type → 𝕊 → IM ValP
parseTy τ s = case τ of
  ℤT pr → do
    let i = HS.read $ chars s ∷ ℤ
    introValP $ IntV pr $ trPrInt pr i
  ListT τ' → do
    vs ← mapM (parseTy τ') $ list $ filter (≢ "") $ splitOn𝕊 "\n" s
    nil ← introValP NilV
    mfoldrOnFrom vs nil $ \ ṽ₁ ṽ₂ → introValP $ ConsV ṽ₁ ṽ₂
  ℙT → do
    kinds ← askL iCxtDeclPrinsL
    prin ← case tohs $ list $ splitOn𝕊 "_" s of
      [ρ] → case kinds ⋕? ρ of
        Some ρκ → return $ case ρκ of
          SinglePK → SinglePEV ρ
          SetPK n → SetPEV n ρ
        None → throwIErrorCxt TypeIError "parseTy: ℙT: [ρ]: kinds ⋕? ρ ≢ Some _" $ frhs
          [ ("kinds",pretty kinds)
          , ("ρ",pretty ρ)
          ]
      [ρ,iS] → case (kinds ⋕? ρ,frhs $ HS.readMaybe $ chars iS) of
        (Some ρκ,Some i) → case ρκ of
          SetPK n | i < n → return $ AccessPEV ρ i
          _ → throwIErrorCxt TypeIError "parseTy: ℙT: [ρ,iS]: (Some _,Some _): ρκ ≢ SetPK n | i < n" $ frhs
            [ ("ρκ",pretty ρκ)
            , ("i",pretty i)
            ]
        _ → throwIErrorCxt TypeIError "parseTy: ℙT: [ρ,iS]: (kinds ≡? ρ,read iS) ≢ (Some _,Some _)" $ frhs
          [ ("kinds",pretty kinds)
          , ("ρ",pretty ρ)
          , ("iS",pretty iS)
          ]
    introValP $ PrinV prin
  _ → throwIErrorCxt NotImplementedIError "parseTy" $ frhs
    [ ("τ",pretty τ)
    ]

-----------
-- MODES --
-----------

--restrictValP ∷ Mode → ValP → ValP
--restrictValP m x̃ = case (m,x̃) of
--  (TopM,_) → x̃
--  (_,AllVP) → AllVP
--  (BotM,_) → BotVP
--  (_,BotVP) → BotVP
--  (SecM ρ,AllVP v) → SecVP ρ v
--  (SecM ρ,SecVP ρ' v) | ρ ≡ ρ' → SecVP ρ' v
--  (SecM ρ,SSecVP ρs v) | ρ ∈ ρs → SecVP ρ v
--  (SecM ρ,ISecVP ρvs) | ρ ∈ keys ρvs → SecVP ρ $ ρvs ⋕! ρ
--  (SSecM ρs,AllVP v) → SSecVP ρs v
--  (SSecM ρs,SecVP ρ' v) | ρ' ∈ ρs → SecVP ρ' v
--  (SSecM ρs,SSecVP ρs' v) → SSecVP (ρs ∩ ρs') v
--  (SSecM ρs,ISecVP ρvs) → ISecVP $ restrict ρs ρvs
--  (_,_) → BotVP

restrictMode ∷ Mode → IM a → IM a
restrictMode m' xM = do
  m ← askL iCxtModeL
  when (not $ m' ⊑ m) $ \ _ → throwIErrorCxt TypeIError "m' ⋢ m" $ frhs
    [ ("m'",pretty m')
    , ("m",pretty m)
    ]
  localL iCxtModeL m' xM

---------------------
-- PARALLEL VALUES --
---------------------

-- bindValP ∷ ValP → (Val → IM ValP) → IM ValP
-- bindValP ṽ f = case ṽ of
--   BotVP → return BotVP
--   AllVP v → f v
--   SecVP ρ v → restrictMode (SecM ρ) $ f v
--   SSecVP ρs v → restrictMode (SSecM ρs) $ f v
--   ISecVP ρvs → 
--     joins ^$ mapMOn (iter ρvs) $ \ (ρ :* v) →
--       restrictMode (SecM ρ) $ f v
--   AllVP → throwIErrorCxt TypeIError "bindValP: ṽ = AllVP" $ frhs
--     [ ("ṽ",pretty ṽ)
--     ]

elimValP ∷ ValP → IM Val
elimValP ṽ = do
  m ← askL iCxtModeL
  case ṽ of
    SSecVP ρs v | m ⊑ SSecM ρs → return v
    AllVP v → return v
    _ → throwIErrorCxt TypeIError "obsValP: ṽ ∉ {AllVP _,SSecVP _ _}" $ frhs
      [ ("ṽ",pretty ṽ)
      ]

modeValP ∷ Mode → Val → ValP
modeValP m v = case m of
  BotM → BotVP
  SecM ρ → SSecVP (single ρ) v
  SSecM ρs → SSecVP ρs v
  TopM → AllVP v

modePrinValPs ∷ Mode → PrinVal ⇰ Val → ValP
modePrinValPs m ρvs = case m of
  BotM → BotVP
  SecM ρ | ρ ∈ keys ρvs → SSecVP (single ρ) $ ρvs ⋕! ρ
         | otherwise → BotVP
  SSecM ρs → ISecVP $ restrict ρs ρvs
  TopM → ISecVP ρvs

introValP ∷ Val → IM ValP
introValP v = do
  m ← askL iCxtModeL
  return $ modeValP m v

restrictValP ∷ ValP → IM ValP
restrictValP ṽ = do
  m ← askL iCxtModeL
  case ṽ of
    SSecVP ρs v | m ⊑ SSecM ρs → return $ modeValP m v
    ISecVP ρvs | m ⊑ SSecM (keys ρvs) → return $ modePrinValPs m ρvs
    AllVP v → return $ modeValP m v
    _ → throwIErrorCxt TypeIError "restrictValP: ṽ ∉ {SSecVP _ _ | m ⊑ ρs,ISecVP _ m ⊑ dom(ρvs) | …,AllVP _}" $ frhs
      [ ("ṽ",pretty ṽ)
      , ("m",pretty m)
      ]

-- bindValsPR ∷ 𝐼 Val → 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
-- bindValsPR vs ṽs f = case ṽs of
--   Nil → f $ list vs
--   ṽ :& ṽs' → bindValP ṽ $ \ v → bindValsPR (vs ⧺ single v) ṽs' f
-- 
-- bindValsP ∷ 𝐿 ValP → (𝐿 Val → IM ValP) → IM ValP
-- bindValsP = bindValsPR null

-----------------
-- APPLICATION --
-----------------

interpApp ∷ ValP → ValP → IM ValP
interpApp ṽ₁ ṽ₂ = do
  v₁ ← elimValP ṽ₁
  case v₁ of 
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

interpPrinVar ∷ 𝕏 → IM PrinExpVal
interpPrinVar x = do
  γ ← askL iCxtEnvL
  kinds ← askL iCxtDeclPrinsL
  case γ ⋕? x of
    Some ṽ → do
      v ← elimValP ṽ
      case v of
        PrinV ρev → return ρev
        _ → throwIErrorCxt TypeIError "interpPrinVar: v ≢ PrinV _" $ frhs
          [ ("v",pretty v)
          ]
        _ → error "BAD"
    None → case 𝕩Gen x of
      None → case kinds ⋕? 𝕩name x of
        Some ρk → return $ case ρk of
          SinglePK → SinglePEV $ 𝕩name x
          SetPK n → SetPEV n $ 𝕩name x
      _ → throwIErrorCxt TypeIError "interpPrinVar: 𝕩Gen x ≢ None" $ frhs
        [ ("x",pretty x)
        ]

interpPrinExp ∷ PrinExp → IM PrinExpVal
interpPrinExp ρe = do
  case ρe of
    VarPE x → interpPrinVar x
    AccessPE x i → do
      ρev ← interpPrinVar x
      case ρev of
        SetPEV n ρx | i < n → return $ AccessPEV ρx i
        _ → throwIErrorCxt TypeIError "interpPrinExp: ρev ≢ SetPEV _ _" $ frhs
          [ ("ρev",pretty ρev)
          ]
    -- case kinds ⋕! p of
    --   SetPK n | i < n → restrictMode (SecM $ AccessPE p i) $ interpExp e'
    --   _ → throwIErrorCxt TypeIError "interpExp: ParE: AccessPE: SinglePK: Cannot access a principal that is not a set." $ frhs
    --     [ ("ρe", pretty ρe)
    --     ]

prinExpVals ∷ PrinExpVal → 𝑃 PrinVal
prinExpVals ρev = case ρev of
  SinglePEV ρ → single $ SinglePV ρ
  SetPEV n ρ → pow $ mapOn (upTo n) $ \ i → AccessPV ρ i
  AccessPEV ρ i → single $ AccessPV ρ i


interpExp ∷ Exp → IM ValP
interpExp e = localL iCxtSourceL (Some $ annotatedTag e) $ case extract e of
  VarE x → restrictValP *$ interpVar x
  BoolE b → introValP $ BoolV b
  StrE s → introValP $ StrV s
  NatE pr n → introValP $ NatV pr $ trPrNat pr n
  IntE pr i → introValP $ IntV pr $ trPrInt pr i
  -- FltE
  BulE → introValP BulV
  IfE e₁ e₂ e₃ → do
    ṽ ← interpExp e₁
    v ← elimValP ṽ
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
    introValP $ PairV ṽ₁ ṽ₂
  NilE → introValP NilV
  ConsE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ ConsV ṽ₁ ṽ₂
  LetTyE _ _ e' → interpExp e'
  LetE ψ e₁ e₂ → do
    ṽ ← interpExp e₁
    bindPat ψ ṽ $ interpExp e₂
  CaseE e' ψes → do
    ṽ ← interpExp e'
    interpCase ṽ ψes
  LamE selfO ψ e' → do
    ξ ← askL iCxtCloL
    introValP $ CloV selfO ψ e' ξ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  -- TLamE
  -- TAppE
  SoloE ρe e' → do
    ρvs ← prinExpVals ^$ interpPrinExp ρe
    case tohs $ list ρvs of
      [ρv] → restrictMode (SecM ρv) $ interpExp e'
      _ → throwIErrorCxt TypeIError "interpExp: SoloE: non-singleton principal set" $ frhs
        [ ("ρvs",pretty ρvs)
        ]
  ParE ρes e' → do
    ρvs ← unions ^$ prinExpVals ^^$ mapM interpPrinExp ρes
    restrictMode (SSecM ρvs) $ interpExp e'
  ShareE φ ρes e' → do
    ρvs ← unions ^$ prinExpVals ^^$ mapM interpPrinExp ρes
    ṽ ← interpExp e'
    v ← elimValP ṽ
    sv ← mpcFrVal v
    return $ ShareVP φ ρvs sv
  {- LOH
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
          SecM ρe → AllVP ^$ parseTy τA $ ioUNSAFE $ read $ "examples-data/" ⧺ prinDataPath ρe ⧺ "/" ⧺ fn
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
  -}

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
  PrinTL ps → do
    let kinds = dict $ mapOn (iter ps) $ \case
          SinglePD ρ → ρ ↦ SinglePK
          ArrayPD ρ n → ρ ↦ SetPK n
    modifyL itlStateDeclPrinsL (kinds ⩌)
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
  -- testInterpreterExample "atq"
  -- testInterpreterExample "atq"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"
