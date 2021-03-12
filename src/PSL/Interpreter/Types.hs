module PSL.Interpreter.Types where

import UVMHS
import AddToUVMHS
import PSL.Syntax

import qualified Prelude as HS

data SProt (p ∷ Prot) where
  SYaoN_P ∷ SProt 'YaoN_P
  SYao2_P ∷ SProt 'Yao2_P

deriving instance Eq (SProt p)
deriving instance Ord (SProt p)
deriving instance Show (SProt p)

data DEq a b where
  YesDEq ∷ (a ~ b) ⇒ DEq a b
  NoDEq ∷ DEq a b

data DCmp a b where
  LTDCmp ∷ DCmp a b
  EQDCmp ∷ (a ~ b) ⇒ DCmp a b
  GTDCmp ∷ DCmp a b

deqSProt ∷ SProt p₁ → SProt p₂ → DEq p₁ p₂
deqSProt sp₁ sp₂ = case (sp₁,sp₂) of
  (SYaoN_P,SYaoN_P) → YesDEq
  (SYao2_P,SYao2_P) → YesDEq
  _ → NoDEq

dcmpSProt ∷ SProt p₁ → SProt p₂ → DCmp p₁ p₂
dcmpSProt sp₁ sp₂ = case (sp₁,sp₂) of
  (SYaoN_P,SYaoN_P) → EQDCmp
  (SYaoN_P,SYao2_P) → LTDCmp
  (SYao2_P,SYaoN_P) → GTDCmp
  (SYao2_P,SYao2_P) → EQDCmp

class 
  ( Eq (MPCPrimVal p)
  , Ord (MPCPrimVal p)
  , Show (MPCPrimVal p)
  ) ⇒ 
  MPCPrim p where
    type MPCPrimVal p ∷ ★
    mpcPrim ∷ P p → Op → 𝐿 (MPCPrimVal p) → IO (MPCPrimVal p)

data MPCVal where
  MPCVal ∷ ∀ p. (MPCPrim p) ⇒ SProt p → MPCPrimVal p → MPCVal

instance Eq MPCVal where
  mpc₁ == mpc₂ = case (mpc₁,mpc₂) of
    (MPCVal (sp₁ ∷ SProt p₁) (v₁ ∷ MPCPrimVal p₁),MPCVal (sp₂ ∷ SProt p₂) (v₂ ∷ MPCPrimVal p₂)) →
      case deqSProt sp₁ sp₂ of
        NoDEq → False
        YesDEq →
          let pr₁ ∷ (SProt p₁,MPCPrimVal p₁)
              pr₁ = (sp₁,v₁) 
              pr₂ ∷ (SProt p₁,MPCPrimVal p₁)
              pr₂ = (sp₂,v₂)
          in pr₁ ≡ pr₂

instance Ord MPCVal where
  compare mpc₁ mpc₂ = case (mpc₁,mpc₂) of
    (MPCVal (sp₁ ∷ SProt p₁) (v₁ ∷ MPCPrimVal p₁),MPCVal (sp₂ ∷ SProt p₂) (v₂ ∷ MPCPrimVal p₂)) →
      case dcmpSProt sp₁ sp₂ of
        LTDCmp → LT
        GTDCmp → GT
        EQDCmp →
          let pr₁ ∷ (SProt p₁,MPCPrimVal p₁)
              pr₁ = (sp₁,v₁) 
              pr₂ ∷ (SProt p₁,MPCPrimVal p₁)
              pr₂ = (sp₂,v₂)
          in compare pr₁ pr₂

deriving instance Show MPCVal

instance MPCPrim 'YaoN_P where
  type MPCPrimVal 'YaoN_P = CktVal
  mpcPrim ∷ P 'YaoN_P → Op → 𝐿 CktVal → IO CktVal
  mpcPrim = undefined

instance MPCPrim 'Yao2_P where
  type MPCPrimVal 'Yao2_P = ()
  mpcPrim ∷ P 'Yao2_P → Op → 𝐿 () → IO ()
  mpcPrim = undefined


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

data CktVal =
    DefaultCV
  | BaseCV Ckt
  | PairCV CktVal CktVal
  | SumCV Ckt CktVal CktVal
  | NilCV
  | ConsCV CktVal CktVal
  | BulCV
  deriving (Eq,Ord,Show)

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
makePrisms ''CktVal
makeLenses ''Ckt
makePrisms ''Input
makePrisms ''Gate
makePrisms ''BaseGate

makePrettySum ''CktVal
makePrettyRecord ''Ckt
makePrettySum ''Input
makePrettySum ''Gate
makePrettySum ''BaseGate

data ShareInfo =
    NotShared
  | Shared Prot (𝑃 PrinVal)
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
  { iParamsLocalMode ∷ Mode
  , iParamsIsExample ∷ 𝔹
  , iParamsVirtualPartyArgs ∷ 𝕊 ⇰ 𝑃 PrinVal
  } deriving (Eq,Ord,Show)
makeLenses ''IParams
makePrettySum ''IParams

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
makePrettySum ''ICxt

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
makePrettySum ''IState

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
makePrettySum ''ResEv
makeLenses ''ResEv

data IOut = IOut
  {
  } deriving (Show)
makePrettySum ''IOut
-- TODO(ins): Ask DD why this wasn't ok w/ empty record
--makeLenses ''IOut

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
  ∷ 𝐿 MPCVal 
  → (∀ a. IM a) 
  → IM b 
  → (∀ p. (MPCPrim p) ⇒ P p → SProt p → 𝐿 (MPCPrimVal p) → IM b) 
  → IM b
sameProts wvs whenBad whenEmpty whenNotEmpty = case wvs of
  Nil → whenEmpty
  MPCVal sp v :& wvs' → do
    vs ← flip error𝑂 whenBad $ sameProts' sp wvs'
    whenNotEmpty P sp $ v :& vs

sameProts' ∷ SProt p → 𝐿 MPCVal → 𝑂 (𝐿 (MPCPrimVal p))
sameProts' sp = mfoldrFromWith null $ \ (MPCVal sp' v) vs →
  case deqSProt sp sp' of
    NoDEq → abort
    YesDEq → return $ v :& vs


-- sameProts vs bad nulCase $ \ p sp v → ... mcpPrim p ...
