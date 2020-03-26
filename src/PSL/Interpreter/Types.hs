module PSL.Interpreter.Types where

import UVMHS
import AddToUVMHS
import PSL.Syntax

------------
-- VALUES --
------------

-- General values
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
  | PrinSetV (𝑃 PrinVal)
  deriving (Eq,Ord,Show)

-- Distributed Values
-- ṽ ∈ dist-val
data ValP =
    SSecVP (𝑃 PrinVal) Val
  | ISecVP (PrinVal ⇰ Val)
  | ShareVP Prot (𝑃 PrinVal) ℕ ValMPC
  | AllVP Val
  | UnknownVP
  deriving (Eq,Ord,Show)

-- Values used in circuits
-- sv ∈ mpc-val
data ValMPC =
    BoolMV 𝔹
  | NatMV IPrecision ℕ
  | IntMV IPrecision ℤ
  | FltMV FPrecision 𝔻
  | PrinMV PrinExpVal
  | PairMV ValMPC ValMPC
  | LMV ValMPC
  | RMV ValMPC
  deriving (Eq,Ord,Show)

------------------
-- TYPES OUTPUT --
------------------

iprecisionSuffix ∷ IPrecision → 𝕊
iprecisionSuffix = \case
  InfIPr → ""
  FixedIPr n₁ n₂ → concat ["#",show𝕊 n₁,".",show𝕊 n₂]

fprecisionSuffix ∷ FPrecision → 𝕊
fprecisionSuffix (FixedFPr n) = concat ["#",show𝕊 n]

iPrecFrFPrec ∷ FPrecision → IPrecision
iPrecFrFPrec (FixedFPr pr) = FixedIPr pr 0

fPrecFrIPrec ∷ IPrecision → FPrecision
fPrecFrIPrec = \case
  InfIPr → FixedFPr 64
  FixedIPr n₁ n₂ → FixedFPr $ n₁ + n₂

getType ∷ Val → 𝕊
getType = \case
  BoolV _ → "bool"
  StrV _ → "string"
  NatV p _ → "nat"⧺iprecisionSuffix p
  IntV p _ → "int"⧺iprecisionSuffix p
  FltV p _ → "flt"⧺fprecisionSuffix p
  BulV → "bul"
  LV _ → "left"
  RV _ → "right"
  PairV _ _ → "pair"
  NilV → "list"
  ConsV _ _ → "list"
  CloV _ _ _ _ → "clo"
  TCloV _ _ _ → "tclo"
  PrinV _ → "prin"
  PrinSetV _ → "prinset"

getTypeMPC ∷ ValMPC → 𝕊
getTypeMPC = \case
  BoolMV _ → "bool"
  NatMV p _ → "nat"⧺iprecisionSuffix p
  IntMV p _ → "int"⧺iprecisionSuffix p
  FltMV p _ → "flt"⧺fprecisionSuffix p
  PrinMV _ → "prin"
  PairMV mv₁ mv₂ → (getTypeMPC mv₁) ⧺ " × " ⧺ (getTypeMPC mv₁)
  LMV mv → "left " ⧺ (getTypeMPC mv)
  RMV mv → "right " ⧺ (getTypeMPC mv)

-----------------
-- ENVIRONMENT --
-----------------

-- Value environment
-- γ ∈ env
type Env = 𝕏 ⇰ ValP

-----------------
-- CLOSURE CXT --
-----------------

-- ξ ∈ clo-cxt
data ICloCxt = ICloCxt
  { iCloCxtEnv ∷ Env
  , iCloCxtMode ∷ Mode
  } deriving (Eq,Ord,Show)

--------------------------------
-- INTERPRETER TOPLEVEL STATE --
--------------------------------

-- γ ∈ itlenv
data ITLEnv = ITLEnv
  { itlEnvDoResources ∷ 𝔹
  }

γtl₀ ∷ ITLEnv
γtl₀ = ITLEnv False

-- σ ∈ itlstate
data ITLState = ITLState
  { itlStateEnv ∷ Env
  , itlStateDeclPrins ∷ Prin ⇰ PrinKind
  } deriving (Eq,Ord,Show)

σtl₀ ∷ ITLState
σtl₀ = ITLState dø dø

-----------------------------
-- INTERPRETER ENVIRONMENT --
-----------------------------

-- ξ̇ ∈ cxt
data ICxt = ICxt
  { iCxtParams ∷ ITLEnv
  , iCxtSource ∷ 𝑂 FullContext
  , iCxtDeclPrins ∷ Prin ⇰ PrinKind
  , iCxtClo ∷ ICloCxt
  }
makeLenses ''ICxt 

ξ₀ ∷ ICxt
ξ₀ = ICxt γtl₀ None dø $ ICloCxt dø TopM

makePrisms ''Val
makePrettySum ''ValP
makePrisms ''ValP
makePrettySum ''ValMPC
makePrisms ''ValMPC
makePrettySum ''ITLEnv
makeLenses ''ITLEnv
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''ICloCxt
makeLenses ''ICloCxt

iCxtEnvL ∷ ICxt ⟢ Env
iCxtEnvL = iCloCxtEnvL ⊚ iCxtCloL

iCxtModeL ∷ ICxt ⟢ Mode
iCxtModeL = iCloCxtModeL ⊚ iCxtCloL

iCxtDoResourcesL ∷ ICxt ⟢ 𝔹
iCxtDoResourcesL = itlEnvDoResourcesL ⊚ iCxtParamsL

------------------------
-- INTERPRETER OUTPUT --
------------------------

data ResEv = ResEv
  { resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 PrinVal
  , resEvPrinsFrom ∷ 𝑃 PrinVal
  , resEvPrinsTo ∷ 𝑃 PrinVal
  , resEvType ∷ 𝕊
  , resEvOp ∷ 𝕊
  , resEvMd ∷ ℕ
  } deriving (Eq,Ord,Show)
makePrettySum ''ResEv
makeLenses ''ResEv

data IOut = IOut
  { iOutResEvs ∷ ResEv ⇰ ℕ
  } deriving (Show)
makePrettySum ''IOut
makeLenses ''IOut

instance Null IOut where null = IOut dø
instance Append IOut where IOut res₁ ⧺ IOut res₂ = IOut $ res₁ + res₂
instance Monoid IOut

-----------------------
-- INTERPRETER ERROR --
-----------------------

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

guardErr ∷ Bool -> IM () -> IM ()
guardErr x im = case x of
  True → skip
  False → im

error𝑂 ∷ 𝑂 a -> IM a -> IM a
error𝑂 e er = case e of
  Some x → return x
  None → er

----------------------
-- EXPRESSION MONAD --
----------------------

newtype IM a = IM { unIM ∷ RWST ICxt IOut () (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ICxt
  , MonadWriter IOut
  , MonadState ()
  , MonadError IError
  , MonadIO
  )

mkIM ∷ (ICxt → IO (IError ∨ (IOut ∧ a))) → IM a
mkIM f = IM $ mkRWST $ \ γ () → ErrorT $ do
  rox ← f γ
  return $ case rox of
    Inl r → Inl r
    Inr (o :* x) → Inr $ () :* o :* x

runIM ∷ ICxt → IM a → IO (IError ∨ (IOut ∧ a))
runIM γ xM = do
  rox ← unErrorT $ runRWST γ () $ unIM xM
  return $ case rox of
    Inl r → Inl r
    Inr (() :* o :* x) → Inr (o :* x)

--------------------
-- TOPLEVEL MONAD --
--------------------

newtype ITLM a = ITLM { unITLM ∷ RWST ITLEnv IOut ITLState (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ITLEnv
  , MonadWriter IOut
  , MonadState ITLState
  , MonadError IError
  , MonadIO
  )

printError ∷ IError → IO ()
printError (IError rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  -- UNCOMMENT TO SEE DUMPED VALUES
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

mkITLM ∷ (ITLEnv → ITLState → IO (IError ∨ (ITLState ∧ IOut ∧ a))) → ITLM a
mkITLM f = ITLM $ mkRWST $ \ γ σ → ErrorT $ f γ σ

runITLM ∷ ITLEnv → ITLState → ITLM a → IO (IError ∨ (ITLState ∧ IOut ∧ a))
runITLM γ σ xM = unErrorT $ runRWST γ σ $ unITLM xM

runITLMIO ∷ ITLEnv → ITLState → ITLM a → IO (ITLState ∧ IOut ∧ a)
runITLMIO γ σ xM = runITLM γ σ xM ≫= \case
  Inl e → printError e ≫ abortIO
  Inr x → return x

evalITLM ∷ ITLEnv → ITLState → ITLM a → IO (IError ∨ a)
evalITLM γ σ = mapp snd ∘ runITLM γ σ

evalITLMIO ∷ ITLEnv → ITLState → ITLM a → IO a
evalITLMIO γ σ = map snd ∘ runITLMIO γ σ

asTLM ∷ IM a → ITLM a
asTLM xM = mkITLM $ \ γtl σ → do
  let ds = itlStateDeclPrins σ
      -- princpal declarations as values
      γ' = dict $ mapOn (iter $ itlStateDeclPrins σ) $ \ (ρ :* κ) → case κ of
        SinglePK → (var ρ ↦) $  AllVP $ PrinV $ ValPEV $ SinglePV ρ
        SetPK n → (var ρ ↦) $  AllVP $ PrinV $ SetPEV n ρ
      -- top-level defs
      γ = itlStateEnv σ
      ξ = compose 
            [ update iCxtEnvL (γ' ⩌ γ)
            , update iCxtDeclPrinsL ds
            , update iCxtParamsL γtl
            ]
            ξ₀
  rox ← runIM ξ xM
  return $ case rox of
    Inl r → Inl r
    Inr (o :* x) → Inr $ σ :* o :* x
