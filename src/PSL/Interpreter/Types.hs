module PSL.Interpreter.Types where

import UVMHS
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
  | PairV ValP ValP
  | LV ValP
  | RV ValP
  | NilV
  | ConsV ValP ValP
  | CloV (𝑂 Var) Pat Exp Env
  | TCloV TVar Exp Env
  | PrinV PrinExpVal
  | PrinSetV (𝑃 PrinVal)
  | LocV Mode ℤ64
  | ArrayV (𝕍 ValP)
  | DefaultV
  | NizkVerifyV (𝑃 PrinVal) ValP
  deriving (Eq,Ord,Show)

-- Distributed Values
-- ṽ ∈ dist-val
data ValP =
    SSecVP (𝑃 PrinVal) Val
  | ISecVP (PrinVal ⇰ Val)
  | ShareVP 𝔹 Prot (𝑃 PrinVal) ValMPC
  | AllVP Val
  | UnknownVP
  | PairVP ValP ValP
  deriving (Eq,Ord,Show)

-- Values used in circuits
-- sv ∈ mpc-val
data ValMPC =
    BaseMV ℕ BaseValMPC
  | PairMV ValMPC ValMPC
  | SumMV ℕ 𝔹 ValMPC ValMPC
  | NilMV
  | ConsMV ValMPC ValMPC
  | DefaultMV
  deriving (Eq,Ord,Show)

data BaseValMPC =
    BoolMV 𝔹
  | NatMV IPrecision ℕ
  | IntMV IPrecision ℤ
  | FltMV FPrecision 𝔻
  | PrinMV PrinVal
  deriving (Eq,Ord,Show)

-----------------
-- ENVIRONMENT --
-----------------

-- Value environment
-- γ ∈ env
type Env = 𝕏 ⇰ ValP

makePrisms ''Val

makePrisms ''ValP
makePrettySum ''ValP

makePrisms ''ValMPC
makePrettySum ''ValMPC

makePrisms ''BaseValMPC
makePrettySum ''BaseValMPC

data ShareInfo = 
    NotShared
  | Shared 𝔹 Prot (𝑃 PrinVal)
  deriving (Eq,Ord,Show)
makePrettySum ''ShareInfo

-----------
-- STORE --
-----------

-- Value Store
-- σ ∈ store
type Store = 𝑊 ValP

-------------
-- PARAMAS --
-------------

-- Interpreter Params
-- θ ∈ params
data IParams = IParams
  { iParamsDoResources ∷ 𝔹
  , iParamsIsExample ∷ 𝔹
  } deriving (Eq,Ord,Show)
makeLenses ''IParams
makePrettySum ''IParams

θ₀ ∷ IParams
θ₀ = IParams False False

-------------
-- CONTEXT --
-------------

-- Interpreter Dynamic Context
-- ξ ∈ cxt
data ICxt = ICxt
  { iCxtParams ∷ IParams
  , iCxtSource ∷ 𝑂 FullContext
  , iCxtDeclPrins ∷ Prin ⇰ PrinKind
  , iCxtEnv ∷ Env
  , iCxtMode ∷ Mode
  , iCxtMPCPathCondition ∷ 𝐿 (ℕ ∧ 𝔹 ∧ ShareInfo)
  } deriving (Show)
makeLenses ''ICxt 
makePrettySum ''ICxt

iCxtDoResourcesL ∷ ICxt ⟢ 𝔹
iCxtDoResourcesL = iParamsDoResourcesL ⊚ iCxtParamsL

iCxtIsExampleL ∷ ICxt ⟢ 𝔹
iCxtIsExampleL = iParamsIsExampleL ⊚ iCxtParamsL

ξ₀ ∷ ICxt
ξ₀ = ICxt θ₀ None dø dø TopM null

-----------
-- STATE --
-----------

-- Interpreter State
-- ω ∈ state
data IState = IState
  { iStateStore ∷ Store
  , iStateNextLoc ∷ ℤ64
  , iStateMPCCont ∷ 𝐿 (𝐿 (ℕ ∧ 𝔹 ∧ ShareInfo) ∧ ShareInfo ∧ ValMPC)
  } deriving (Eq,Ord,Show)
makeLenses ''IState
makePrettySum ''IState

ω₀ ∷ IState
ω₀ = IState wø (𝕫64 1) null

------------
-- OUTPUT --
------------

data ResEv = ResEv
  { resEvZK ∷ 𝔹
  , resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 PrinVal
  , resEvPrinsFrom ∷ 𝑃 PrinVal
  , resEvPrinsTo ∷ 𝑃 PrinVal
  , resEvType ∷ 𝕊
  , resEvTypeFrom ∷ 𝕊
  , resEvTypeTo ∷ 𝕊
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

guardErr ∷ (Monad m,MonadError IError m) ⇒ Bool -> m () -> m ()
guardErr x im = case x of
  True → skip
  False → im

error𝑂 ∷ (Monad m,MonadError IError m) ⇒ 𝑂 a -> m a -> m a
error𝑂 e er = case e of
  Some x → return x
  None → er

--------------------
-- TOPLEVEL STATE --
--------------------

-- ωtl ∈ tl-state
data ITLState = ITLState
  { itlStateDeclPrins ∷ Prin ⇰ PrinKind
  , itlStateEnv ∷ Env
  , itlStateExp ∷ IState
  } deriving (Eq,Ord,Show)
makeLenses ''ITLState
makePrettySum ''ITLState

ωtl₀ ∷ ITLState
ωtl₀ = ITLState dø dø ω₀

----------------------
-- EXPRESSION MONAD --
----------------------

newtype IM a = IM { unIM ∷ RWST ICxt IOut IState (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ICxt
  , MonadWriter IOut
  , MonadState IState
  , MonadError IError
  , MonadIO
  )

mkIM ∷ (ICxt → IState → IO (IError ∨ (IState ∧ IOut ∧ a))) → IM a
mkIM f = IM $ mkRWST $ ErrorT ∘∘ f

runIM ∷ ICxt → IState → IM a → IO (IError ∨ (IState ∧ IOut ∧ a))
runIM ξ ω = unErrorT ∘ runRWST ξ ω ∘ unIM

--------------------
-- TOPLEVEL MONAD --
--------------------

newtype ITLM a = ITLM { unITLM ∷ RWST IParams IOut ITLState (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader IParams
  , MonadWriter IOut
  , MonadState ITLState
  , MonadError IError
  , MonadIO
  )

printError ∷ IError → IO ()
printError (IError rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

mkITLM ∷ (IParams → ITLState → IO (IError ∨ (ITLState ∧ IOut ∧ a))) → ITLM a
mkITLM f = ITLM $ mkRWST $ \ θ ωtl → ErrorT $ f θ ωtl

runITLM ∷ IParams → ITLState → ITLM a → IO (IError ∨ (ITLState ∧ IOut ∧ a))
runITLM θ ωtl xM = unErrorT $ runRWST θ ωtl $ unITLM xM

runITLMIO ∷ IParams → ITLState → 𝕊 → ITLM a → IO (ITLState ∧ IOut ∧ a)
runITLMIO θ ωtl name xM = runITLM θ ωtl xM ≫= \case
  Inr x → return x
  Inl e → do 
    pprint $ ppHorizontal [ppErr ">",ppBD $ ppString name]
    printError e 
    abortIO

evalITLM ∷ IParams → ITLState → ITLM a → IO (IError ∨ a)
evalITLM θ ωtl = mapp snd ∘ runITLM θ ωtl

evalITLMIO ∷ IParams → ITLState → 𝕊 → ITLM a → IO a
evalITLMIO θ ωtl name = map snd ∘ runITLMIO θ ωtl name

asTLM ∷ IM a → ITLM a
asTLM xM = mkITLM $ \ θ ωtl → do
  let ds = itlStateDeclPrins ωtl
      -- princpal declarations as values
      γ' = dict $ mapOn (iter $ itlStateDeclPrins ωtl) $ \ (ρ :* κ) → case κ of
        SinglePK → (var ρ ↦) $  AllVP $ PrinV $ ValPEV $ SinglePV ρ
        SetPK n → (var ρ ↦) $  AllVP $ PrinV $ SetPEV n ρ
      -- top-level defs
      γ = itlStateEnv ωtl
      ξ = compose 
            [ update iCxtEnvL (γ' ⩌ γ)
            , update iCxtDeclPrinsL ds
            , update iCxtParamsL θ
            ]
            ξ₀
      ω = itlStateExp ωtl
  rox ← runIM ξ ω xM
  return $ case rox of
    Inl r → Inl r
    Inr (ω' :* o :* x) → Inr $ update itlStateExpL ω' ωtl :* o :* x
