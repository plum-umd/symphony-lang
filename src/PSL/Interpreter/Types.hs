module PSL.Interpreter.Types where

import UVMHS
import AddToUVMHS
import PSL.Syntax

import qualified Prelude as HS

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
  | UnknownV Type
  deriving (Eq,Ord,Show)

-- Distributed Values
-- ṽ ∈ dist-val
data ValP =
    SSecVP (𝑃 PrinVal) Val            -- values which are the same on parties (not shares)
  | ISecVP (PrinVal ⇰ Val)            -- values which are different on parties (bundles, not shares)
  | ShareVP (𝑃 PrinVal) MPCVal        -- shares
  | AllVP Val                         -- special case, equivalent to SSecVP ⊤ Val
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
  ) ⇒
  Protocol p where
    type ProtocolVal p ∷ ★
    exePrim ∷ P p → Op → 𝐿 (ProtocolVal p) → IO (ProtocolVal p)

-- Shares
-- sh ∈ share p
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

instance Protocol 'YaoN_P where
  type ProtocolVal 'YaoN_P = Ckt
  exePrim ∷ P 'YaoN_P → Op → 𝐿 Ckt → IO Ckt
  exePrim = undefined

instance Protocol 'Yao2_P where
  type ProtocolVal 'Yao2_P = ()
  exePrim ∷ P 'Yao2_P → Op → 𝐿 () → IO ()
  exePrim = undefined

data Ckt = Ckt
  { gatesC ∷ Wire ⇰ Gate
  , outC   ∷ Wire
  } deriving (Eq,Ord,Show)

data Input =
    AvailableI BaseGate
  | UnavailableI Type
  deriving (Eq,Ord,Show)

-- Gates. Note: Wires are inputs to the gate
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
  | PrinBG (AddBTD PrinVal)
  deriving (Eq,Ord,Show)

type Wire = ℕ64

 -----------------
-- ENVIRONMENT --
-----------------

-- Value environment
-- γ ∈ env
type Env = 𝕏 ⇰ ValP

makePrisms ''Val
makePrisms ''ValP
makePrisms ''MPCVal
makeLenses ''Ckt
makePrisms ''Input
makePrisms ''Gate
makePrisms ''BaseGate

data ShareInfo =
    NotShared
  | Shared Prot (𝑃 PrinVal)
  deriving (Eq,Ord,Show)

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
  { iParamsLocalMode ∷ Mode
  , iParamsIsExample ∷ 𝔹
  , iParamsVirtualPartyArgs ∷ 𝕊 ⇰ 𝑃 PrinVal
  } deriving (Eq,Ord,Show)
makeLenses ''IParams

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
  , iCxtMPCPathCondition ∷ 𝐿 (Ckt ∧ ShareInfo)
  } deriving (Show)
makeLenses ''ICxt

iCxtIsExampleL ∷ ICxt ⟢ 𝔹
iCxtIsExampleL = iParamsIsExampleL ⊚ iCxtParamsL

iCxtLocalModeL ∷ ICxt ⟢ Mode
iCxtLocalModeL = iParamsLocalModeL ⊚ iCxtParamsL

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
  , iStateMPCCont ∷ 𝐿 (𝐿 (Ckt ∧ ShareInfo) ∧ ShareInfo ∧ Ckt)
  } deriving (Eq,Ord,Show)
makeLenses ''IState

iStateShareInfoNextWireL ∷ ((Mode ⇰ Wire) ∧ Mode) ⟢ Wire
iStateShareInfoNextWireL = lens getCkt setCkt
  where getCkt (ws :* m)   = case lookup𝐷 ws m of
                             None   → HS.fromIntegral 0
                             Some w → w
        setCkt (ws :* m) w = (m ↦ w) ⩌ ws :* m

iStateShareInfoNextWiresL ∷ Mode → IState ⟢ ((Mode ⇰ Wire) ∧ Mode)
iStateShareInfoNextWiresL m = lens getCkts setCkts
  where getCkts st = access iStateNextWiresL st :* m
        setCkts st (ws :* _m) = update iStateNextWiresL ws st

iStateNextWireL ∷ Mode → IState ⟢ Wire
iStateNextWireL m = iStateShareInfoNextWireL ⊚ (iStateShareInfoNextWiresL m)

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
makeLenses ''ResEv

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
asTLM xM = do
  vps ← askL iParamsVirtualPartyArgsL
  mkITLM $ \ θ ωtl → do
    let ds = itlStateDeclPrins ωtl
        -- princpal declarations as values
        γ' = dict $ mapOn (iter $ itlStateDeclPrins ωtl) $ \ (ρ :* κ) → case κ of
          SinglePK → (var ρ ↦) $ AllVP $ PrinV $ ValPEV $ SinglePV ρ
          SetPK n → (var ρ ↦) $ AllVP $ PrinV $ SetPEV n ρ
          VirtualPK → (var ρ ↦) $ AllVP $ PrinV $ case vps ⋕? ρ of
            Some ρv → PowPEV ρv
            None → ValPEV $ VirtualPV ρ
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

-- extra stuff --

sameProts
  ∷ 𝐿 Share
  → (∀ a. IM a)
  → IM b
  → (∀ p. (Protocol p) ⇒ P p → SProt p → 𝐿 (ProtocolVal p) → IM b)
  → IM b
sameProts shs whenBad whenEmpty whenNotEmpty = case shs of
  Nil → whenEmpty
  Share sp pv :& shs' → do
    pvs ← flip error𝑂 whenBad $ sameProts' sp shs'
    whenNotEmpty P sp $ pv :& pvs

sameProts' ∷ SProt p → 𝐿 Share → 𝑂 (𝐿 (ProtocolVal p))
sameProts' sp = mfoldrFromWith null $ \ (Share sp' pv) pvs →
  case deq sp sp' of
    NoDEq → abort
    YesDEq → return $ pv :& pvs


-- sameProts vs bad nulCase $ \ p sp v → ... mcpPrim p ...
