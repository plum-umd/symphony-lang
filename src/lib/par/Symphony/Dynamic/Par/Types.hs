module Symphony.Dynamic.Par.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Channel
import Symphony.Dynamic.Par.GMW

import qualified Crypto.Random as R
import Foreign.ForeignPtr (ForeignPtr)

-------------
--- VALUE ---
-------------

data Val =
    KnownV ValR
  | UnknownV

data ValR =
    BaseV BaseVal
  | ProdV Val Val
  | SumV BaseVal Val Val
  | ListV (𝐿 Val)
  | CloV (𝑂 Var) (NoEq ((IM Val Val → IM Val Val) → Val → IM Val Val))
  | LocV Mode (ℝMut Val ∨ 𝕍Mut Val)
  | BundleV (PrinVal ⇰ Val)
  | DefaultV

data BaseVal =
    ClearV ClearBaseVal
  | EncV (𝑃 PrinVal) EncBaseVal

data ClearBaseVal =
    BulV
  | BoolV 𝔹
  | NatV IPrecision ℕ
  | IntV IPrecision ℤ
  | FltV FPrecision 𝔻
  | StrV 𝕊
  | PrinV PrinVal
  | PrinSetV PrinSetVal
  deriving (Eq, Ord, Show)

data EncBaseVal =
    GmwV Gmw
  | YaoV Yao

type Yao = ()

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
  , iParamsMe        ∷ PrinVal
  } deriving (Eq, Ord, Show)

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
  , iStateSessionsGmw  ∷ 𝑃 PrinVal ⇰ GmwSession
  , iStateMPCCont      ∷ 𝐿 (𝐿 v ∧ v)
  }

------------
-- OUTPUT --
------------

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

----------------------
-- EXPRESSION MONAD --
----------------------

newtype IM v a = IM { unIM ∷ RWST (ICxt v) IOut (IState v) (ErrorT IError IO) a }
  deriving
  ( Functor
  , Return, Bind, Monad
  , MonadReader (ICxt v)
  , MonadWriter IOut
  , MonadState (IState v)
  , MonadError IError
  , MonadIO
  )

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

-- Val

makePrisms ''Val

instance Pretty Val where
  pretty = \case
    KnownV v → pretty v
    UnknownV → ppCon "⋆"

elimKnown ∷ Val → IM Val ValR
elimKnown ṽ = error𝑂 (view knownVL ṽ) $
              throwIErrorCxt TypeIError "elimKnown: view knownVL ṽ ≡ None" $ frhs
              [ ("ṽ", pretty ṽ)
              ]

-- ValR

makePrisms ''ValR

instance Pretty ValR where
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

-- TODO: Move intro/elim forms from Operations.hs here

-- BaseVal

makePrisms ''BaseVal

instance Pretty BaseVal where
  pretty = \case
    ClearV bv → pretty bv
    EncV ρvs bv →
      ppPostF concat levelMODE
      (ppSetBotLevel $ concat
       [ ppPun "{"
       , concat $ inbetween (ppPun ",") $ map pretty $ iter ρvs
       , ppPun "}"
       ]) $
      pretty bv

elimClear ∷ (STACK) ⇒ BaseVal → IM Val ClearBaseVal
elimClear = \case
  ClearV cbv    → return cbv
  EncV _ρ𝑃 _ebv → throwIErrorCxt TypeIError "elimClear: E" empty𝐿

elimEnc ∷ (STACK) ⇒ 𝑃 PrinVal → BaseVal → IM Val EncBaseVal
elimEnc ρsₑ = \case
  ClearV _cbv  → throwIErrorCxt TypeIError "elimEncrypted: C" empty𝐿
  EncV ρsₐ ebv → do
    guardErr (ρsₑ ≡ ρsₐ) $
      throwIErrorCxt TypeIError "elimEncrypted: ρvsₑ ≢ ρvsₐ" $ frhs
      [ ("ρvsₑ", pretty ρsₑ)
      , ("ρvsₐ", pretty ρsₐ)
      ]
    return ebv

metaBaseVal ∷ (STACK) ⇒ BaseVal → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaBaseVal = \case
  ClearV _cbv        → None
  EncV ρ𝑃 (GmwV _gmw) → Some $ GMWP  :* ρ𝑃
  EncV ρ𝑃 (YaoV _gmw) → Some $ YaoNP :* ρ𝑃

metaMeet ∷ (STACK) ⇒ 𝑂 (Prot ∧ 𝑃 PrinVal) → 𝑂 (Prot ∧ 𝑃 PrinVal) → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaMeet meta₁ meta₂ = case (meta₁, meta₂) of
  (None      , None      ) → None
  (Some _φρ𝑃₁, None      ) → meta₁
  (None      , Some _φρ𝑃₂) → meta₂
  (Some _φρ𝑃₁, Some _φρ𝑃₂) → meta₁

metaBaseVals ∷ (STACK) ⇒ 𝐿 BaseVal → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaBaseVals = foldFromWith None $ \ bv acc → metaMeet (metaBaseVal bv) acc

-- ClearBaseVal

makePrisms ''ClearBaseVal

instance Pretty ClearBaseVal where
  pretty = \case
    BulV         → ppCon "•"
    BoolV b      → pretty b
    NatV p n     → ppNatSymphony p n
    IntV p i     → ppIntSymphony p i
    FltV p d     → ppFltSymphony p d
    StrV s       → pretty s
    PrinV ρv     → pretty ρv
    PrinSetV ρsv → pretty ρsv

elimBool ∷ (STACK) ⇒ ClearBaseVal → IM Val 𝔹
elimBool cbv = error𝑂 (view boolVL cbv) $
               throwIErrorCxt TypeIError "elimBool: view boolVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimNat ∷ (STACK) ⇒ ClearBaseVal → IM Val (IPrecision ∧ ℕ)
elimNat cbv = error𝑂 (view natVL cbv) $
              throwIErrorCxt TypeIError "elimNat: view natVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

elimStr ∷ (STACK) ⇒ ClearBaseVal → IM Val 𝕊
elimStr cbv = error𝑂 (view strVL cbv) $
              throwIErrorCxt TypeIError "elimStr: view strVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

elimPrin ∷ (STACK) ⇒ ClearBaseVal → IM Val PrinVal
elimPrin cbv = error𝑂 (view prinVL cbv) $
               throwIErrorCxt TypeIError "elimPrin: view prinVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimPrinSet ∷ (STACK) ⇒ ClearBaseVal → IM Val PrinSetVal
elimPrinSet cbv = error𝑂 (view prinSetVL cbv) $
                  throwIErrorCxt TypeIError "elimPrinSet: view prinSetVL cbv ≡ None" $ frhs
                  [ ("cbv", pretty cbv)
                  ]

typeFrClearBaseVal ∷ ClearBaseVal → BaseType
typeFrClearBaseVal = \case
  BulV          → UnitT
  BoolV _b      → 𝔹T
  NatV pr _n    → ℕT pr
  IntV pr _i    → ℤT pr
  FltV pr _f    → 𝔽T pr
  StrV _s       → 𝕊T
  PrinV _ρv     → ℙT
  PrinSetV _ρsv → ℙsT

defaultClearBaseVal ∷ BaseType → ClearBaseVal
defaultClearBaseVal = \case
  UnitT → BulV
  𝔹T    → BoolV null
  ℕT pr → NatV pr null
  ℤT pr → IntV pr null
  𝔽T pr → FltV pr null
  𝕊T    → StrV null
  ℙT    → undefined -- TODO
  ℙsT   → undefined -- TODO

-- EncBaseVal

makePrisms ''EncBaseVal

instance Pretty EncBaseVal where
  pretty ebv = case ebv of
    GmwV gmw → prettyProt GMWP gmw
    YaoV yao → prettyProt YaoNP yao
    where prettyProt φ sh =
            ppPostF concat levelMODE
            (ppSetBotLevel $ concat
             [ ppPun "⌈"
             , pretty φ
             , ppPun "⌉"
             ]) $
            pretty sh

elimGmw ∷ EncBaseVal → IM Val Gmw
elimGmw ebv = error𝑂 (view gmwVL ebv) $
              throwIErrorCxt TypeIError "elimGmw: view gmwVL ebv ≡ None" $ frhs
              [ ("ebv", pretty ebv)
              ]

-- IParams

makeLenses ''IParams

makePrettySum ''IParams

θ₀ ∷ PrinVal → IParams
θ₀ ρv = IParams False ρv

-- ICxt

makeLenses ''ICxt

makePrettySum ''ICxt

ξ₀ ∷ IParams → ICxt v
ξ₀ θ = ICxt θ None null null top null

instance HasLens (ICxt v) (𝑂 SrcCxt) where
  hasLens = iCxtSourceL

iCxtIsExampleL ∷ ICxt v ⟢ 𝔹
iCxtIsExampleL = iParamsIsExampleL ⊚ iCxtParamsL

iCxtMeL ∷ ICxt v ⟢ PrinVal
iCxtMeL = iParamsMeL ⊚ iCxtParamsL

-- IState

makeLenses ''IState

makePrettySum ''IState

ω₀ ∷ R.ChaChaDRG → IState v
ω₀ g = IState wø (𝕫64 1) g dø dø null

-- IOut

makePrettySum ''IOut

-- ITLState

makeLenses ''ITLState

makePrettySum ''ITLState

ωtl₀ ∷ R.ChaChaDRG → ITLState v
ωtl₀ g = ITLState dø pø 0 (ω₀ g)

-- IM

mkIM ∷ (ICxt v → IState v → IO (IError ∨ (IState v ∧ IOut ∧ a))) → IM v a
mkIM f = IM $ mkRWST $ ErrorT ∘∘ f

runIM ∷ ICxt v → IState v → IM v a → IO (IError ∨ (IState v ∧ IOut ∧ a))
runIM ξ ω = unErrorT ∘ runRWST ξ ω ∘ unIM

-- ITLM

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

printError ∷ IError → IO ()
printError (IError rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

evalITLM ∷ IParams → ITLState v → ITLM v a → IO (IError ∨ a)
evalITLM θ ωtl = mapp snd ∘ runITLM θ ωtl

evalITLMIO ∷ IParams → ITLState v → 𝕊 → ITLM v a → IO a
evalITLMIO θ ωtl name = map snd ∘ runITLMIO θ ωtl name

getGmwSession ∷ 𝑃 PrinVal → IM Val (𝑂 GmwSession)
getGmwSession ρvs = do
  πs ← getL iStateSessionsGmwL
  return $ πs ⋕? ρvs

mkGmwSession ∷ 𝑃 PrinVal → IM Val GmwSession
mkGmwSession ρvs = do
  π ← todoCxt
  modifyL iStateSessionsGmwL ((ρvs ↦ π) ⩌!)
  return π

getOrMkGmwSession ∷ 𝑃 PrinVal → IM Val GmwSession
getOrMkGmwSession ρvs = do
  π𝑂 ← getGmwSession ρvs
  case π𝑂 of
    None   → mkGmwSession ρvs
    Some π → return π

-- PrinVal

makePrisms ''PrinVal

-- PrinSetVal

makePrisms ''PrinSetVal

elimPrinArr ∷ (STACK) ⇒ PrinSetVal → IM Val (Prin ∧ ℕ)
elimPrinArr ρsv = error𝑂 (view arrPSVL ρsv) $
              throwIErrorCxt TypeIError "elimArr: view arrPSVL ρsv ≡ None" $ frhs
              [ ("ρsv", pretty ρsv)
              ]

elimPSV ∷ (STACK) ⇒ PrinSetVal → 𝑃 PrinVal
elimPSV = \case
  PowPSV ρ𝑃  → ρ𝑃
  ArrPSV ρ n → pow [ AccessPV ρ i | i ← [0..(n - 1)] ]

-- Types

baseTL ∷ Type ⌲ BaseType
baseTL = prism constr destr
  where constr bτ = BaseT bτ
        destr = \case
          BaseT bτ → Some bτ
          _        → None

pairTL ∷ Type ⌲ Type ∧ Type
pairTL = prism constr destr
  where constr (τ₁ :* τ₂) = τ₁ :×: τ₂
        destr = \case
          τ₁ :×: τ₂ → Some $ τ₁ :* τ₂
          _ → None

sumTL ∷ Type ⌲ Type ∧ Type
sumTL = prism constr destr
  where constr (τ₁ :* τ₂) = τ₁ :+: τ₂
        destr = \case
          τ₁ :+: τ₂ → Some $ τ₁ :* τ₂
          _ → None

listTL ∷ Type ⌲ (ℕ ∧ Type)
listTL = prism constr destr
  where constr (n :* τ) = ListT n τ
        destr = \case
          ListT n τ → Some (n :* τ)
          _ → None

arrTL ∷ Type ⌲ (ℕ ∧ Type)
arrTL = prism constr destr
  where constr (n :* τ) = ArrT n τ
        destr = \case
          ArrT n τ → Some (n :* τ)
          _ → None
