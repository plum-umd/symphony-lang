module Symphony.Dynamic.Par.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Prg.Types
import Symphony.Dynamic.Par.Channel.Types
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
    BulCV
  | BoolCV 𝔹
  | NatCV IPrecision ℕ
  | IntCV IPrecision ℤ
  | FltCV FPrecision 𝔻
  | StrCV 𝕊
  | PrinCV PrinVal
  | PrinSetCV PrinSetVal
  deriving (Eq, Ord, Show)

data EncBaseVal =
    BulEV EncBul
  | BoolEV EncBool

data EncBul =
    GmwEBul

data EncBool =
    GmwEB GmwBool

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
  { iParamsName      ∷ 𝕊
  , iParamsMe        ∷ PrinVal
  , iParamsPrg       ∷ Prg
  , iParamsChannels  ∷ PrinVal ⇰ Channel
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
  { iStateNextLoc ∷ ℤ64
  , iStateStore   ∷ (Store v)
  , iStateGmws    ∷ 𝑃 PrinVal ⇰ Gmw
  , iStateMPCCont ∷ 𝐿 (𝐿 v ∧ v)
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

-- Val

makePrisms ''Val

instance Pretty Val where
  pretty = \case
    KnownV v → pretty v
    UnknownV → ppCon "★"

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

elimBaseVal ∷ (STACK) ⇒ 𝑃 PrinVal → (ClearBaseVal → IM Val a) → (EncBaseVal → IM Val a) → BaseVal → IM Val a
elimBaseVal ρvsₑ kC kE = \case
  ClearV cbv    → kC cbv
  EncV ρvsₐ ebv → do
    guardErr (ρvsₑ ≡ ρvsₐ) $
      throwIErrorCxt TypeIError "elimEncrypted: ρvsₑ ≢ ρvsₐ" $ frhs
      [ ("ρvsₑ", pretty ρvsₑ)
      , ("ρvsₐ", pretty ρvsₐ)
      ]
    kE ebv

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

metaProt ∷ (STACK) ⇒ EncBaseVal → Prot
metaProt = \case
  BulEV GmwEBul    → GMWP
  BoolEV (GmwEB _) → GMWP

metaBaseVal ∷ (STACK) ⇒ BaseVal → 𝑂 (𝑃 PrinVal ∧ Prot)
metaBaseVal = \case
  ClearV _cbv → None
  EncV ρ𝑃 ebv → Some $ ρ𝑃 :* metaProt ebv

metaMeet ∷ (STACK) ⇒ 𝑂 (𝑃 PrinVal ∧ Prot) → 𝑂 (𝑃 PrinVal ∧ Prot) → 𝑂 (𝑃 PrinVal ∧ Prot)
metaMeet meta₁ meta₂ = case (meta₁, meta₂) of
  (None      , None      ) → None
  (Some _φρ𝑃₁, None      ) → meta₁
  (None      , Some _φρ𝑃₂) → meta₂
  (Some _φρ𝑃₁, Some _φρ𝑃₂) → meta₁

metaBaseVals ∷ (STACK) ⇒ 𝐿 BaseVal → 𝑂 (𝑃 PrinVal ∧ Prot)
metaBaseVals = foldFromWith None $ \ bv → metaMeet (metaBaseVal bv)

-- ClearBaseVal

makePrisms ''ClearBaseVal

instance Pretty ClearBaseVal where
  pretty = \case
    BulCV         → ppCon "•"
    BoolCV b      → pretty b
    NatCV p n     → ppNatSymphony p n
    IntCV p i     → ppIntSymphony p i
    FltCV p d     → ppFltSymphony p d
    StrCV s       → pretty s
    PrinCV ρv     → pretty ρv
    PrinSetCV ρsv → pretty ρsv

elimBool ∷ (STACK) ⇒ ClearBaseVal → IM Val 𝔹
elimBool cbv = error𝑂 (view boolCVL cbv) $
               throwIErrorCxt TypeIError "elimBool: view boolVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimNat ∷ (STACK) ⇒ ClearBaseVal → IM Val (IPrecision ∧ ℕ)
elimNat cbv = error𝑂 (view natCVL cbv) $
              throwIErrorCxt TypeIError "elimNat: view natVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

elimStr ∷ (STACK) ⇒ ClearBaseVal → IM Val 𝕊
elimStr cbv = error𝑂 (view strCVL cbv) $
              throwIErrorCxt TypeIError "elimStr: view strVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

elimPrin ∷ (STACK) ⇒ ClearBaseVal → IM Val PrinVal
elimPrin cbv = error𝑂 (view prinCVL cbv) $
               throwIErrorCxt TypeIError "elimPrin: view prinVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimPrinSet ∷ (STACK) ⇒ ClearBaseVal → IM Val PrinSetVal
elimPrinSet cbv = error𝑂 (view prinSetCVL cbv) $
                  throwIErrorCxt TypeIError "elimPrinSet: view prinSetVL cbv ≡ None" $ frhs
                  [ ("cbv", pretty cbv)
                  ]

typeFrClearBaseVal ∷ ClearBaseVal → BaseType
typeFrClearBaseVal = \case
  BulCV          → UnitT
  BoolCV _b      → 𝔹T
  NatCV pr _n    → ℕT pr
  IntCV pr _i    → ℤT pr
  FltCV pr _f    → 𝔽T pr
  StrCV _s       → 𝕊T
  PrinCV _ρv     → ℙT
  PrinSetCV _ρsv → ℙsT

defaultClearBaseVal ∷ BaseType → ClearBaseVal
defaultClearBaseVal = \case
  UnitT → BulCV
  𝔹T    → BoolCV null
  ℕT pr → NatCV pr null
  ℤT pr → IntCV pr null
  𝔽T pr → FltCV pr null
  𝕊T    → StrCV null
  ℙT    → undefined -- TODO
  ℙsT   → undefined -- TODO

-- EncBaseVal

makePrisms ''EncBaseVal

instance Pretty EncBaseVal where
  pretty ebv = case ebv of
    BulEV bul     → pretty bul
    BoolEV b      → pretty b

prettyProt ∷ (Pretty a) ⇒ Prot → a → Doc
prettyProt φ x =
  ppPostF concat levelMODE
  (ppSetBotLevel $ concat
    [ ppPun "⌈"
    , pretty φ
    , ppPun "⌉"
    ]) $
  pretty x

-- EncBul

makePrisms ''EncBul

instance Pretty EncBul where
  pretty ebul = case ebul of
    GmwEBul → prettyProt GMWP UnitT

elimGmwBul ∷ EncBul → IM Val ()
elimGmwBul ebul = error𝑂 (view gmwEBulL ebul) $
                   throwIErrorCxt TypeIError "elimGmwEBul: view gmwEBulL ebul ≡ None" $ frhs
                   [ ("ebul", pretty ebul)
                   ]

-- EncBool

makePrisms ''EncBool

instance Pretty EncBool where
  pretty eb = case eb of
    GmwEB b → prettyProt GMWP b

elimGmwBool ∷ EncBool → IM Val GmwBool
elimGmwBool eb = error𝑂 (view gmwEBL eb) $
               throwIErrorCxt TypeIError "elimGmwBool: view gmwEBL eb ≡ None" $ frhs
               [ ("eb", pretty eb)
               ]

-- IParams

makeLenses ''IParams

makePrettySum ''IParams

θ₀ ∷ 𝕊 → PrinVal → Prg → (PrinVal ⇰ Channel) → IParams
θ₀ = IParams

-- ICxt

makeLenses ''ICxt

makePrettySum ''ICxt

ξ₀ ∷ IParams → ICxt v
ξ₀ θ = ICxt θ None null null top null

instance HasLens (ICxt v) (𝑂 SrcCxt) where
  hasLens = iCxtSourceL

iCxtMeL ∷ ICxt v ⟢ PrinVal
iCxtMeL = iParamsMeL ⊚ iCxtParamsL

iCxtPrgL ∷ ICxt v ⟢ Prg
iCxtPrgL = iParamsPrgL ⊚ iCxtParamsL

iCxtChannelsL ∷ ICxt v ⟢ (PrinVal ⇰ Channel)
iCxtChannelsL = iParamsChannelsL ⊚ iCxtParamsL

getPrg ∷ (STACK) ⇒ IM Val Prg
getPrg = askL iCxtPrgL

getChannel ∷ (STACK) ⇒ PrinVal → IM Val Channel
getChannel ρv = do
  chans ← askL iCxtChannelsL
  fromSomeCxt $ chans ⋕? ρv

getChannels ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (PrinVal ⇰ Channel)
getChannels ρvs = dict ^$ mapM (\ ρv → (ρv ↦) ^$ getChannel ρv) $ iter ρvs

-- IState

makeLenses ''IState

makePrettySum ''IState

ω₀ ∷ IState v
ω₀ = IState (𝕫64 1) wø dø null

getGmw ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (𝑂 Gmw)
getGmw ρvs = do
  gmws ← getL iStateGmwsL
  return $ gmws ⋕? ρvs

mkGmw ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val Gmw
mkGmw ρvs = do
  me ← askL iCxtMeL
  chans ← getChannels ρvs
  gmw ← gmwProtocolNew me chans
  modifyL iStateGmwsL ((ρvs ↦ gmw) ⩌!)
  return gmw

getOrMkGmw ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val Gmw
getOrMkGmw ρvs = do
  gmw𝑂 ← getGmw ρvs
  case gmw𝑂 of
    None     → mkGmw ρvs
    Some gmw → return gmw

-- IOut

makePrettySum ''IOut

-- IM

--mkIM ∷ (ICxt v → IState v → IO (IError ∨ (IState v ∧ IOut ∧ a))) → IM v a
--mkIM f = IM $ mkRWST $ ErrorT ∘∘ f

runIM ∷ IParams → IM v a → IO (IError ∨ (IState v ∧ IOut ∧ a))
runIM θ = unErrorT ∘ runRWST (ξ₀ θ) ω₀ ∘ unIM

runIMIO ∷ IParams → IM v a → IO (IState v ∧ IOut ∧ a)
runIMIO θ xM = runIM θ xM ≫= \case
  Inr x → return x
  Inl e → do
    pprint $ ppHorizontal [ppErr ">", ppBD $ ppString (iParamsName θ)]
    printError e
    abortIO

printError ∷ IError → IO ()
printError (IError rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

evalIM ∷ IParams → IM v a → IO (IError ∨ a)
evalIM θ = mapp snd ∘ runIM θ

evalIMIO ∷ IParams → IM v a → IO a
evalIMIO = mapp snd ∘ runIMIO

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
