module Symphony.Interpreter.Types where

import Symphony.Prelude

import Symphony.Syntax
import Symphony.Interpreter.Error
import Symphony.Interpreter.Pretty
import Symphony.Interpreter.BaseVal.Types

import qualified Crypto.Random as R
import Foreign.ForeignPtr (ForeignPtr)

class (Pretty (EBV v), Pretty v) ⇒ Value v where
  type EBV v ∷ ★

  introVal   ∷ (STACK) ⇒ ValR v (EBV v) → IM v v
  elimVal    ∷ (STACK) ⇒ v → IM v (ValR v (EBV v))
  unknownVal ∷ (STACK) ⇒ v
  locateVal  ∷ (STACK) ⇒ v → IM v v
  inPrins    ∷ (STACK) ⇒ 𝑃 PrinVal → IM v 𝔹

  shareVal  ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → v → Type → IM v v
  commVal   ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → v → Type → IM v v
  flushVal  ∷ (STACK) ⇒ PrinVal → IM v ()
  revealVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → v → Type → IM v v

  embedEBV ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM v (EBV v)
  primEBV  ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 (EBV v) → IM v (EBV v)

--------------
--- Values ---
--------------

data ValR v e =
    BaseV (BaseVal e)
  | ProdV v v
  | SumV (BaseVal e) v v
  | ListV (𝐿 v)
  | CloV (𝑂 Var) (NoEq ((IM v v → IM v v) → v → IM v v))
  | LocV Mode (ℝMut v ∨ 𝕍Mut v)
  | BundleV (PrinVal ⇰ v)
  | DefaultV

instance (Pretty v, Pretty e) ⇒ Pretty (ValR v e) where
  pretty = \case
    BaseV bv → pretty bv
    ProdV ṽₗ ṽᵣ → pretty (ṽₗ :* ṽᵣ)
    SumV bvₜ ṽₗ ṽᵣ → ppInfr levelCOND
      (ppSeparated
         [ ppCon "?"
         , pretty ṽₗ
         , ppCon "◇"
         ])
      (pretty bvₜ) $
      pretty ṽᵣ
    ListV ṽs → pretty ṽs
    CloV self𝑂 _f → concat [pretty self𝑂, ppCon "λ<clo>"]
    LocV m ℓ → ppApp (ppCon "loc") [pretty m,pretty ℓ]
    BundleV ρvs →
      ppCollection (ppPun "⟪") (ppPun "⟫") (ppPun ";") $
      mapOn (iter ρvs) $ \ (ρ :* ṽ) →
                           concat
                           [ ppAlign $ pretty ρ
                           , ppSpaceIfBreak
                           , ppPun "|"
                           , ppSpaceIfBreak
                           , ppAlign $ pretty ṽ
                           ]

    DefaultV → ppCon "⊥"


---------------
--- Channel ---
---------------

data ChannelStruct = ChannelStruct deriving (Eq,Ord,Show)
type Channel = ForeignPtr ChannelStruct

----------------------
--- EMP FFI Values ---
----------------------

data EMPProtocolStruct = EMPProtocolStruct deriving (Eq, Ord, Show)
type EMPProtocol       = ForeignPtr EMPProtocolStruct

data EMPBoolStruct = EMPBoolStruct deriving (Eq, Ord, Show)
type EMPBool       = ForeignPtr EMPBoolStruct

data EMPIntStruct = EMPIntStruct deriving (Eq, Ord, Show)
type EMPInt       = ForeignPtr EMPIntStruct

data EMPFltStruct = EMPFltStruct deriving (Eq, Ord, Show)
type EMPFlt       = ForeignPtr EMPFltStruct

data EMPVal =
    BoolEV EMPBool
  | NatEV IPrecision EMPInt -- Unfortunately, EMP doesn't support ℕ so we represent them as integers
  | IntEV IPrecision EMPInt
  | FltEV FPrecision EMPFlt
  deriving (Eq,Ord,Show)

instance Pretty EMPVal where
  pretty = \case
    BoolEV _  → ppCon "𝔹"
    NatEV p _ → concat [ppCon "ℕ",pretty p]
    IntEV p _ → concat [ppCon "ℤ",pretty p]
    FltEV p _ → concat [ppCon "𝔽",pretty p]

----------------------
--- MP-SPDZ FFI Values ---
----------------------

data MPSPDZProtocolStruct = MPSPDZProtocolStruct deriving (Eq,Ord,Show)
type MPSPDZProtocol = ForeignPtr MPSPDZProtocolStruct

data MPSPDZInt = MPSPDZInt deriving (Eq,Ord,Show)

data MPSPDZVal =
    IntMPSPDZV (ForeignPtr MPSPDZInt)
  | NatMPSPDZV (ForeignPtr MPSPDZInt)
  deriving (Eq,Ord,Show)

instance Pretty MPSPDZVal where
  pretty = \case
    IntMPSPDZV _ → ppCon "ℤ64"
    NatMPSPDZV _ → ppCon "ℕ64"

--------------
-- Circuits --
--------------

data Ckt = Ckt
  { inputsC  ∷ PrinVal ⇰ (Wire ⇰ Input)
  , gatesC   ∷ Wire ⇰ Gate
  , outputC  ∷ Wire
  } deriving (Eq,Ord,Show)

data Input =
    AvailableI ClearBaseVal
  | UnavailableI BaseType
  deriving (Eq,Ord,Show)

data Gate =
    BaseG ClearBaseVal
  | PrimG Op (𝐿 Wire)
  deriving (Eq,Ord,Show)

type Wire = ℕ

-----------------
-- ENVIRONMENT --
-----------------

-- Value environment
-- γ ∈ env
type Env v = 𝕏 ⇰ v

-----------
-- STORE --
-----------

-- Value Store
-- σ ∈ store
type Store v = 𝑉 v

------------
-- PARAMS --
------------

-- Interpreter Params
-- θ ∈ params
data IParams = IParams
  { iParamsIsExample ∷ 𝔹
  , iParamsMe        ∷ 𝑂 PrinVal
  } deriving (Eq,Ord,Show)

θ₀ ∷ IParams
θ₀ = IParams False None

-------------
-- CONTEXT --
-------------

-- Interpreter Dynamic Context
-- ξ ∈ cxt
data ICxt v = ICxt
  { iCxtParams           ∷ IParams
  , iCxtSource           ∷ 𝑂 SrcCxt
  , iCxtEnv              ∷ (Env v)
  , iCxtPrinScope        ∷ 𝑃 PrinVal
  , iCxtMode             ∷ Mode
  , iCxtMPCPathCondition ∷ 𝐿 v
  } deriving (Show)

ξ₀ ∷ ICxt v
ξ₀ = ICxt θ₀ None null null top null

-----------
-- STATE --
-----------

-- Interpreter State
-- ω ∈ state
data IState v = IState
  { iStateStore        ∷ (Store v)
  , iStateNextLoc      ∷ ℤ64
  , iStateGen          ∷ R.ChaChaDRG
  , iStateChannels     ∷ PrinVal ⇰ Channel
  , iStateNextWires    ∷ (𝑃 PrinVal) ⇰ Wire
  , iStateSessionsYao  ∷ 𝑃 PrinVal ⇰ EMPProtocol
  , iStateSessionsSPDZ ∷ 𝑃 PrinVal ⇰ MPSPDZProtocol
  , iStateMPCCont      ∷ 𝐿 (𝐿 v ∧ v)
  }

ω₀ ∷ R.ChaChaDRG → IState v
ω₀ g = IState wø (𝕫64 1) g dø dø dø dø null

------------
-- OUTPUT --
------------

data ResEv = ResEv
  { resEvProt      ∷ Prot
  , resEvPrins     ∷ 𝑃 PrinVal
  , resEvPrinsFrom ∷ 𝑃 PrinVal
  , resEvPrinsTo   ∷ 𝑃 PrinVal
  , resEvType      ∷ 𝕊
  , resEvTypeFrom  ∷ 𝕊
  , resEvTypeTo    ∷ 𝕊
  , resEvOp        ∷ 𝕊
  } deriving (Eq,Ord,Show)

data IOut = IOut
  {
  } deriving (Show)

instance Null IOut where null = IOut
instance Append IOut where IOut ⧺ IOut = IOut
instance Monoid IOut

--------------------
-- TOPLEVEL STATE --
--------------------

-- ωtl ∈ tl-state
data ITLState v = ITLState
  { itlStateEnv       ∷ (Env v)
  , itlStatePrinScope ∷ 𝑃 PrinVal
  , itlStateNextId    ∷ ℕ
  , itlStateExp       ∷ (IState v)
  }

ωtl₀ ∷ R.ChaChaDRG → ITLState v
ωtl₀ g = ITLState dø pø 0 (ω₀ g)

----------------------
-- EXPRESSION MONAD --
----------------------

newtype IM v a = IM { unIM ∷ RWST (ICxt v) IOut (IState v) (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader (ICxt v)
  , MonadWriter IOut
  , MonadState (IState v)
  , MonadError IError
  , MonadIO
  )

mkIM ∷ (ICxt v → IState v → IO (IError ∨ (IState v ∧ IOut ∧ a))) → IM v a
mkIM f = IM $ mkRWST $ ErrorT ∘∘ f

runIM ∷ ICxt v → IState v → IM v a → IO (IError ∨ (IState v ∧ IOut ∧ a))
runIM ξ ω = unErrorT ∘ runRWST ξ ω ∘ unIM

--------------------
-- TOPLEVEL MONAD --
--------------------

newtype ITLM v a = ITLM { unITLM ∷ RWST IParams IOut (ITLState v) (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader IParams
  , MonadWriter IOut
  , MonadState (ITLState v)
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

mkITLM ∷ (IParams → ITLState v → IO (IError ∨ (ITLState v ∧ IOut ∧ a))) → ITLM v a
mkITLM f = ITLM $ mkRWST $ \ θ ωtl → ErrorT $ f θ ωtl

runITLM ∷ IParams → ITLState v → ITLM v a → IO (IError ∨ (ITLState v ∧ IOut ∧ a))
runITLM θ ωtl xM = unErrorT $ runRWST θ ωtl $ unITLM xM

runITLMIO ∷ IParams → ITLState v → 𝕊 → ITLM v a → IO (ITLState v ∧ IOut ∧ a)
runITLMIO θ ωtl name xM = runITLM θ ωtl xM ≫= \case
  Inr x → return x
  Inl e → do
    pprint $ ppHorizontal [ppErr ">",ppBD $ ppString name]
    printError e
    abortIO

evalITLM ∷ IParams → ITLState v → ITLM v a → IO (IError ∨ a)
evalITLM θ ωtl = mapp snd ∘ runITLM θ ωtl

evalITLMIO ∷ IParams → ITLState v → 𝕊 → ITLM v a → IO a
evalITLMIO θ ωtl name = map snd ∘ runITLMIO θ ωtl name

makeLenses ''IParams

makeLenses ''ICxt

instance HasLens (ICxt v) (𝑂 SrcCxt) where
  hasLens = iCxtSourceL

iCxtIsExampleL ∷ ICxt v ⟢ 𝔹
iCxtIsExampleL = iParamsIsExampleL ⊚ iCxtParamsL

iCxtMeL ∷ ICxt v ⟢ 𝑂 PrinVal
iCxtMeL = iParamsMeL ⊚ iCxtParamsL

makePrettyRecord ''Ckt
makePrettySum ''Input
makePrettySum ''Gate

makePrettySum ''IParams
makePrettySum ''ICxt
makePrettySum ''IState
makePrettySum ''ResEv
makePrettySum ''IOut
makePrettySum ''ITLState
makePrisms ''ValR
