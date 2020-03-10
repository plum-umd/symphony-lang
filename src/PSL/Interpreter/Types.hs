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
  { iCxtSource ∷ 𝑂 FullContext
  , iCxtDeclPrins ∷ Prin ⇰ PrinKind
  , iCxtClo ∷ ICloCxt
  }
makeLenses ''ICxt 

ξ₀ ∷ ICxt
ξ₀ = ICxt None dø $ ICloCxt dø TopM

-- makePrettySum ''Val
makePrettySum ''Val
makePrisms ''Val
makePrettySum ''ValP
makePrisms ''ValP
makePrettySum ''ValMPC
makePrisms ''ValMPC
makePrettySum ''ITLState
makeLenses ''ITLState
makePrettySum ''ICloCxt
makeLenses ''ICloCxt

iCxtEnvL ∷ ICxt ⟢ Env
iCxtEnvL = iCloCxtEnvL ⊚ iCxtCloL

iCxtModeL ∷ ICxt ⟢ Mode
iCxtModeL = iCloCxtModeL ⊚ iCxtCloL

------------------------
-- INTERPRETER OUTPUT --
------------------------

data ResEv = ResEv
  { resEvProt ∷ Prot
  , resEvPrins ∷ 𝑃 PrinVal
  , resEvType ∷ 𝕊
  , resEvOp ∷ 𝕊
  , resEvMultDepth ∷ ℕ
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

newtype ITLM a = ITLM { unITLM ∷ RWST () IOut ITLState (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return,Bind,Monad
  , MonadReader ()
  , MonadWriter IOut
  , MonadState ITLState
  , MonadError IError
  , MonadIO
  )

mkITLM ∷ (ITLState → IO (IError ∨ (ITLState ∧ IOut ∧ a))) → ITLM a
mkITLM f = ITLM $ mkRWST $ \ () σ → ErrorT $ f σ

runITLM ∷ ITLState → ITLM a → IO (IError ∨ (ITLState ∧ IOut ∧ a))
runITLM σ xM = unErrorT $ runRWST () σ $ unITLM xM

evalITLM ∷ ITLState → ITLM a → IO (IError ∨ a)
evalITLM σ = mapp snd ∘ runITLM σ

evalITLMIO ∷ ITLState → ITLM a → IO a
evalITLMIO σ xM = 
  evalITLM σ xM ≫= \case
    Inl (IError rsO cs rc rm) → do
      pprint $ ppVertical $ concat
        [ single𝐼 $ ppHeader $ show𝕊 rc
        , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
        -- UNCOMMENT TO SEE DUMPED VALUES
        -- , single𝐼 $ rm
        , single𝐼 $ pretty cs
        ]
      abortIO
    Inr x → return x

asTLM ∷ IM a → ITLM a
asTLM xM = mkITLM $ \ σ → do
  let ds = itlStateDeclPrins σ
      -- princpal declarations as values
      γ' = dict $ mapOn (iter $ itlStateDeclPrins σ) $ \ (ρ :* κ) → case κ of
        SinglePK → (var ρ ↦) $  AllVP $ PrinV $ ValPEV $ SinglePV ρ
        SetPK n → (var ρ ↦) $  AllVP $ PrinV $ SetPEV n ρ
      -- top-level defs
      γ = itlStateEnv σ
      ξ = update iCxtEnvL (γ' ⩌ γ) $
          update iCxtDeclPrinsL ds $
          ξ₀
  rox ← runIM ξ xM
  return $ case rox of
    Inl r → Inl r
    Inr (o :* x) → Inr $ σ :* o :* x
