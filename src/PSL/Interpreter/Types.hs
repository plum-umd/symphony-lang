module PSL.Interpreter.Types where

import UVMHS
import AddToUVMHS
import PSL.Syntax

import qualified Prelude as HS

import Network.Socket (Socket, PortNumber)
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.ForeignPtr (ForeignPtr)

------------
-- VALUES --
------------

-- General values
-- v ∈ val
data Val =
    DefaultV
  | BulV
  | BaseV BaseVal
  | StrV 𝕊
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
  | ArrayV (𝑉 ValP)
  | UnknownV
  deriving (Eq,Ord,Show)

data BaseVal =
    BoolBV 𝔹
  | NatBV IPrecision ℕ
  | IntBV IPrecision ℤ
  | FltBV FPrecision 𝔻
  deriving (Eq,Ord,Show)

typeOfBaseVal ∷ BaseVal → BaseType
typeOfBaseVal = \case
  BoolBV _b → 𝔹T
  NatBV pr _n → ℕT pr
  IntBV pr _i → ℤT pr
  FltBV pr _f → 𝔽T pr

defaultBaseValOf ∷ BaseType → BaseVal
defaultBaseValOf = \case
  𝔹T → BoolBV False
  ℕT pr → NatBV pr 0
  ℤT pr → IntBV pr $ HS.fromIntegral 0
  𝔽T pr → FltBV pr $ HS.fromIntegral 0

-- Distributed Values
-- ṽ ∈ dist-val
data ValP where
  SSecVP  ∷ Mode → Val → ValP                                         -- Values
  ISecVP  ∷ (PrinVal ⇰ Val) → ValP                                    -- Bundles
  ShareVP ∷ ∀ p. (Protocol p) ⇒ SProt p → 𝑃 PrinVal → MPCVal p → ValP -- Shares

instance Eq ValP where
  ṽ₁ == ṽ₂ = case (ṽ₁, ṽ₂) of
    (SSecVP m₁ v₁, SSecVP m₂ v₂) → m₁ ≡ m₂ ⩓ v₁ ≡ v₂
    (ISecVP b₁, ISecVP b₂) → b₁ ≡ b₂
    (ShareVP φ₁ ρvs₁ v̂₁, ShareVP φ₂ ρvs₂ v̂₂) →
      case deq φ₁ φ₂ of
        NoDEq  → False
        YesDEq → ρvs₁ ≡ ρvs₂ ⩓ v̂₁ ≡ v̂₂
    _ → False

instance Ord ValP where
  compare ṽ₁ ṽ₂ = case (ṽ₁, ṽ₂) of
    (SSecVP m₁ v₁, SSecVP m₂ v₂) →
      case compare m₁ m₂ of
        LT → LT
        GT → GT
        EQ → compare v₁ v₂
    (SSecVP _ _, _) → LT
    (ISecVP _, SSecVP _ _) → GT
    (ISecVP b₁, ISecVP b₂) → compare b₁ b₂
    (ISecVP _, ShareVP _ _ _) → LT
    (ShareVP φ₁ ρvs₁ v̂₁, ShareVP φ₂ ρvs₂ v̂₂) →
      case dcmp φ₁ φ₂ of
        LTDCmp → LT
        GTDCmp → GT
        EQDCmp →
          case compare ρvs₁ ρvs₂ of
            LT → LT
            GT → GT
            EQ → compare v̂₁ v̂₂
    (ShareVP _ _ _, _) → GT

deriving instance (Show ValP)

data ValS where
  SSecVS  ∷ Val → ValS                                                -- Values
  ISecVS  ∷ (PrinVal ⇰ Val) → ValS                                    -- Bundles
  ShareVS ∷ ∀ p. (Protocol p) ⇒ SProt p → 𝑃 PrinVal → MPCVal p → ValS -- Shares

instance Eq ValS where
  ṽ₁ == ṽ₂ = case (ṽ₁, ṽ₂) of
    (SSecVS v₁, SSecVS v₂) → v₁ ≡ v₂
    (ISecVS b₁, ISecVS b₂) → b₁ ≡ b₂
    (ShareVS φ₁ ρvs₁ v̂₁, ShareVS φ₂ ρvs₂ v̂₂) →
      case deq φ₁ φ₂ of
        NoDEq  → False
        YesDEq → ρvs₁ ≡ ρvs₂ ⩓ v̂₁ ≡ v̂₂
    _ → False

instance Ord ValS where
  compare ṽ₁ ṽ₂ = case (ṽ₁, ṽ₂) of
    (SSecVS v₁, SSecVS v₂) → compare v₁ v₂
    (SSecVS _, _) → LT
    (ISecVS _, SSecVS _) → GT
    (ISecVS b₁, ISecVS b₂) → compare b₁ b₂
    (ISecVS _, ShareVS _ _ _) → LT
    (ShareVS φ₁ ρvs₁ v̂₁, ShareVS φ₂ ρvs₂ v̂₂) →
      case dcmp φ₁ φ₂ of
        LTDCmp → LT
        GTDCmp → GT
        EQDCmp →
          case compare ρvs₁ ρvs₂ of
            LT → LT
            GT → GT
            EQ → compare v̂₁ v̂₂
    (ShareVS _ _ _, _) → GT

deriving instance (Show ValS)

data ShareInfo p = ShareInfo
  { proxySI ∷ P p
  , protSI  ∷ SProt p
  , prinsSI ∷ 𝑃 PrinVal
  }

deriving instance (Eq (ShareInfo p))
deriving instance (Ord (ShareInfo p))
deriving instance (Show (ShareInfo p))

-- MPC Values
-- v̂ ∈ mpc-val
data MPCVal p where
  DefaultMV ∷ MPCVal p
  BulMV     ∷ MPCVal p
  BaseMV    ∷ (Protocol p) ⇒ (ProtocolVal p) → MPCVal p
  PairMV    ∷ MPCVal p → MPCVal p → MPCVal p
  SumMV     ∷ (Protocol p) ⇒ (ProtocolVal p) → MPCVal p → MPCVal p → MPCVal p
  NilMV     ∷ MPCVal p
  ConsMV    ∷ MPCVal p → MPCVal p → MPCVal p

deriving instance (Eq (MPCVal p))
deriving instance (Ord (MPCVal p))
deriving instance (Show (MPCVal p))

-- MPC Protocols
class
  ( Eq (ProtocolVal p)
  , Ord (ProtocolVal p)
  , Show (ProtocolVal p)
  , Pretty (ProtocolVal p)
  ) ⇒
  Protocol p where
    type ProtocolVal p ∷ ★

    typeOf       ∷                                                                                      P p → ProtocolVal p                                 → BaseType
    shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P p → PrinVal       → 𝑃 PrinVal → BaseVal           → m (ProtocolVal p)
    shareUnk     ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P p → PrinVal       → 𝑃 PrinVal → BaseType          → m (ProtocolVal p)
    embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P p → 𝑃 PrinVal     → BaseVal                       → m (ProtocolVal p)
    exePrim      ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P p → 𝑃 PrinVal     → Op        → 𝐿 (ProtocolVal p) → m (ProtocolVal p)
    reveal       ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P p → 𝑃 PrinVal     → PrinVal   → MPCVal p          → m Val

----------------------
--- EMP FFI Values ---
----------------------

data NetIOStruct = NetIOStruct deriving (Eq,Ord,Show)
type NetIO = Ptr NetIOStruct -- Cannot be ForeignPtr because EMP holds an internal reference

data SemiHonestStruct = SemiHonestStruct deriving (Eq,Ord,Show)
type SemiHonest = Ptr SemiHonestStruct

data EMPSession = EMPSession
  { channelES    ∷ NetIO
  , semiHonestES ∷ SemiHonest
  } deriving (Eq,Ord,Show)

data EMPBool = EMPBool deriving (Eq,Ord,Show)
data EMPInt  = EMPInt  deriving (Eq,Ord,Show)
data EMPFlt  = EMPFlt  deriving (Eq,Ord,Show)

data EMPVal =
    BoolEV (ForeignPtr EMPBool)
  | NatEV IPrecision (ForeignPtr EMPInt) -- Unfortunately, EMP doesn't support ℕ so we represent them as integers
  | IntEV IPrecision (ForeignPtr EMPInt)
  | FltEV FPrecision (ForeignPtr EMPFlt)
  deriving (Eq,Ord,Show)

--------------
-- Circuits --
--------------

data Ckt = Ckt
  { inputsC  ∷ PrinVal ⇰ (Wire ⇰ Input)
  , gatesC   ∷ Wire ⇰ Gate
  , outputC  ∷ Wire
  } deriving (Eq,Ord,Show)

data Input =
    AvailableI BaseVal
  | UnavailableI BaseType
  deriving (Eq,Ord,Show)

data Gate =
    BaseG BaseVal
  | PrimG Op (𝐿 Wire)
  deriving (Eq,Ord,Show)

type Wire = ℕ

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
type Store = 𝑉 ValP

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
  , iCxtSource ∷ 𝑂 SrcCxt
  , iCxtDeclPrins ∷ Prin ⇰ PrinKind
  , iCxtEnv ∷ Env
  , iCxtGlobalMode ∷ Mode
  , iCxtPrinIds ∷ PrinVal ⇰ ℕ
  , iCxtMPCPathCondition ∷ 𝐿 ValP
  } deriving (Show)

ξ₀ ∷ ICxt
ξ₀ = ICxt θ₀ None dø dø TopM dø null

-----------
-- STATE --
-----------

-- Interpreter State
-- ω ∈ state
data IState = IState
  { iStateStore ∷ Store
  , iStateNextLoc ∷ ℤ64
  , iStateListenSock ∷ 𝑂 Socket
  , iStateNextWires ∷ (𝑃 PrinVal) ⇰ Wire
  , iStateSessionsYao ∷ PrinVal ⇰ EMPSession
  , iStateMPCCont ∷ 𝐿 (𝐿 ValP ∧ ValP)
  } deriving (Eq,Show)

ω₀ ∷ IState
ω₀ = IState wø (𝕫64 1) None dø dø null

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
  { iErrorSource ∷ 𝑂 SrcCxt
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
  , itlStateNextId ∷ ℕ
  , itlStatePrinIds ∷ PrinVal ⇰ ℕ
  , itlStateEnv ∷ Env
  , itlStateExp ∷ IState
  } deriving (Eq,Show)

ωtl₀ ∷ ITLState
ωtl₀ = ITLState dø 0 dø dø ω₀

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
