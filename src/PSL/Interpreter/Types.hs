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
    BaseV BaseVal
  | StrV 𝕊
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
  | UnknownV Type
  deriving (Eq,Ord,Show)

data BaseVal =
    BoolBV 𝔹
  | NatBV IPrecision ℕ
  | IntBV IPrecision ℤ
  | FltBV FPrecision 𝔻
  deriving (Eq,Ord,Show)

-- Distributed Values
-- ṽ ∈ dist-val
data ValP =
    SSecVP Mode Val                   -- values which are the same on parties (not shares)
  | ISecVP (PrinVal ⇰ Val)            -- values which are different on parties (bundles, not shares)
  | ShareVP Prot (𝑃 PrinVal) MPCVal   -- shares
  deriving (Eq,Ord,Show)

data UnShare =
    NotShared Val
  | Shared Prot (𝑃 PrinVal) MPCVal
  deriving (Eq,Ord,Show)

-- MPC Values
-- v̂ ∈ mpc-val
data MPCVal =
    DefaultMV
  | BaseMV Share
  | PairMV MPCVal MPCVal
  | SumMV Share MPCVal MPCVal
  | NilMV
  | ConsMV MPCVal MPCVal
  | BulMV
  deriving (Eq,Ord,Show)

-- MPC Protocols
class
  ( Eq (ProtocolVal p)
  , Ord (ProtocolVal p)
  , Show (ProtocolVal p)
  , Pretty (ProtocolVal p)
  ) ⇒
  Protocol p where
    type ProtocolVal p ∷ ★

    typeOf ∷ P p → ProtocolVal p → IM BaseType

    exeBaseVal ∷ P p → 𝑂 PrinVal → BaseVal → IM (ProtocolVal p)
    exeUnk ∷ P p → PrinVal → BaseType → IM (ProtocolVal p)
    exePrim ∷ P p → Op → 𝐿 (ProtocolVal p) → IM (ProtocolVal p)

    reveal ∷ P p → 𝑃 PrinVal → ProtocolVal p → IM BaseVal

-- Shares
-- sh ∈ share
data Share where
  Share ∷ ∀ p. (Protocol p) ⇒ SProt p → ProtocolVal p → Share

instance Eq Share where
  sh₁ == sh₂ = case (sh₁, sh₂) of
    (Share (sp₁ ∷ SProt p₁) (pv₁ ∷ ProtocolVal p₁), Share (sp₂ ∷ SProt p₂) (pv₂ ∷ ProtocolVal p₂)) →
      case deq sp₁ sp₂ of
        NoDEq → False
        YesDEq →
          let pr₁ ∷ (SProt p₁, ProtocolVal p₁)
              pr₁ = (sp₁, pv₁)
              pr₂ ∷ (SProt p₁, ProtocolVal p₁)
              pr₂ = (sp₂, pv₂)
          in pr₁ ≡ pr₂

instance Ord Share where
  compare sh₁ sh₂ = case (sh₁, sh₂) of
    (Share (sp₁ ∷ SProt p₁) (pv₁ ∷ ProtocolVal p₁), Share (sp₂ ∷ SProt p₂) (pv₂ ∷ ProtocolVal p₂)) →
      case dcmp sp₁ sp₂ of
        LTDCmp → LT
        GTDCmp → GT
        EQDCmp →
          let pr₁ ∷ (SProt p₁, ProtocolVal p₁)
              pr₁ = (sp₁, pv₁)
              pr₂ ∷ (SProt p₁, ProtocolVal p₁)
              pr₂ = (sp₂, pv₂)
          in compare pr₁ pr₂

deriving instance Show Share

--------------
-- Circuits --
--------------

data Ckt = Ckt
  { gatesC ∷ Wire ⇰ Gate
  , outC   ∷ Wire
  } deriving (Eq,Ord,Show)

data Input =
    AvailableI BaseGate
  | UnavailableI BaseType
  deriving (Eq,Ord,Show)

data Gate =
    BaseG BaseGate
  | InputG (𝑃 PrinVal) Input
  | PrimG Op (𝐿 Wire)
  deriving (Eq,Ord,Show)

data BaseGate =
    BoolBG 𝔹
  | NatBG IPrecision ℕ
  | IntBG IPrecision ℤ
  | FltBG FPrecision 𝔻
  deriving (Eq,Ord,Show)

type Wire = ℕ64

-----------------
-- ENVIRONMENT --
-----------------

-- Value environment
-- γ ∈ env
type Env = 𝕏 ⇰ ValP

-----------
-- STORE --
-----------

-- Value Store
-- σ ∈ store
type Store = 𝑊 ValP

------------
-- PARAMS --
------------

-- Interpreter Params
-- θ ∈ params
data IParams = IParams
  { iParamsLocalMode ∷ Mode
  , iParamsIsExample ∷ 𝔹
  , iParamsVirtualPartyArgs ∷ 𝕊 ⇰ 𝑃 PrinVal
  } deriving (Eq,Ord,Show)

θ₀ ∷ IParams
θ₀ = IParams TopM False dø

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
  , iCxtGlobalMode ∷ Mode
  , iCxtMPCPathCondition ∷ 𝐿 UnShare
  } deriving (Show)

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
  , iStateNextWires ∷ Mode ⇰ Wire
  , iStateMPCCont ∷ 𝐿 (𝐿 UnShare ∧ UnShare)
  } deriving (Eq,Ord,Show)

ω₀ ∷ IState
ω₀ = IState wø (𝕫64 1) dø null

------------
-- OUTPUT --
------------

data ResEv = ResEv
  { resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 PrinVal
  , resEvPrinsFrom ∷ 𝑃 PrinVal
  , resEvPrinsTo ∷ 𝑃 PrinVal
  , resEvType ∷ 𝕊
  , resEvTypeFrom ∷ 𝕊
  , resEvTypeTo ∷ 𝕊
  , resEvOp ∷ 𝕊
  } deriving (Eq,Ord,Show)

data IOut = IOut
  {
  } deriving (Show)

instance Null IOut where null = IOut
instance Append IOut where IOut ⧺ IOut = IOut
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

-- r ∈ cerr
data IError = IError
  { iErrorSource ∷ 𝑂 FullContext
  , iErrorCallStack ∷ CallStack
  , iErrorClass ∷ IErrorClass
  , iErrorMsg ∷ Doc
  }

--------------------
-- TOPLEVEL STATE --
--------------------

-- ωtl ∈ tl-state
data ITLState = ITLState
  { itlStateDeclPrins ∷ Prin ⇰ PrinKind
  , itlStateEnv ∷ Env
  , itlStateExp ∷ IState
  } deriving (Eq,Ord,Show)

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
