module Symphony.Dynamic.Par.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Prg
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
  | SumV BoolVal Val Val
  | ListV (𝐿 Val)
  | CloV (𝑂 Var) (NoEq ((IM Val Val → IM Val Val) → Val → IM Val Val))
  | LocV Mode (ℝMut Val ∨ 𝕍Mut Val)
  | BundleV (PrinVal ⇰ Val)
  | DefaultV

data BaseVal =
    BulV
  | BoolV BoolVal
  | NatV IPrecision NatVal
  | IntV IPrecision IntVal
  | StrV 𝕊
  | PrinV PrinVal
  | PrinSetV PrinSetVal

data BoolVal =
    ClearBV 𝔹
  | EncBV (𝑃 PrinVal) EncBool

data EncBool =
    GmwB GmwBool

data NatVal =
    ClearNV ℕ
  | EncNV (𝑃 PrinVal) EncNat

data EncNat =
    GmwN GmwNat

data IntVal =
    ClearZV ℤ
  | EncZV (𝑃 PrinVal) EncInt

data EncInt =
    GmwZ GmwInt

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
  , iParamsConfigs   ∷ PrinVal ⇰ (Addr ∧ Port)
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
  , iStatePrgs    ∷ 𝑃 PrinVal ⇰ Prg
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
    LocV m (Inl r) → ppApp (ppCon "ref") [pretty m, pretty r]
    LocV m (Inr a) → ppApp (ppCon "array") [pretty m, pretty a]
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

elimBase ∷ ValR → IM Val BaseVal
elimBase v = error𝑂 (view baseVL v) $
             throwIErrorCxt TypeIError "elimBase: view baseVL v ≣ None" $ frhs
             [ ("v", pretty v)
             ]

-- TODO: Move intro/elim forms from Operations.hs here

{-
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
-}
-- BaseVal

makePrisms ''BaseVal

instance Pretty BaseVal where
  pretty = \case
    BulV         → ppCon "•"
    BoolV b      → pretty b
    NatV p n     → ppNatSymphony p n
    IntV p i     → ppIntSymphony p i
    StrV s       → pretty s
    PrinV ρv     → pretty ρv
    PrinSetV ρsv → pretty ρsv

elimBool ∷ (STACK) ⇒ BaseVal → IM Val BoolVal
elimBool bv = error𝑂 (view boolVL bv) $
               throwIErrorCxt TypeIError "elimBool: view boolVL bv ≡ None" $ frhs
               [ ("bv", pretty bv)
               ]

elimNat ∷ (STACK) ⇒ BaseVal → IM Val (IPrecision ∧ NatVal)
elimNat bv = error𝑂 (view natVL bv) $
              throwIErrorCxt TypeIError "elimNat: view natVL bv ≡ None" $ frhs
              [ ("bv", pretty bv)
              ]

elimInt ∷ (STACK) ⇒ BaseVal → IM Val (IPrecision ∧ IntVal)
elimInt bv = error𝑂 (view intVL bv) $
              throwIErrorCxt TypeIError "elimInt: view intVL bv ≡ None" $ frhs
              [ ("bv", pretty bv)
              ]

elimStr ∷ (STACK) ⇒ BaseVal → IM Val 𝕊
elimStr bv = error𝑂 (view strVL bv) $
              throwIErrorCxt TypeIError "elimStr: view strVL bv ≡ None" $ frhs
              [ ("bv", pretty bv)
              ]

elimPrin ∷ (STACK) ⇒ BaseVal → IM Val PrinVal
elimPrin bv = error𝑂 (view prinVL bv) $
               throwIErrorCxt TypeIError "elimPrin: view prinVL bv ≡ None" $ frhs
               [ ("bv", pretty bv)
               ]

elimPrinSet ∷ (STACK) ⇒ BaseVal → IM Val PrinSetVal
elimPrinSet bv = error𝑂 (view prinSetVL bv) $
                  throwIErrorCxt TypeIError "elimPrinSet: view prinSetVL bv ≡ None" $ frhs
                  [ ("bv", pretty bv)
                  ]

typeFrBaseVal ∷ BaseVal → BaseType
typeFrBaseVal = \case
  BulV          → UnitT
  BoolV _b      → 𝔹T
  NatV pr _n    → ℕT pr
  IntV pr _i    → ℤT pr
  StrV _s       → 𝕊T
  PrinV _ρv     → ℙT
  PrinSetV _ρsv → ℙsT

defaultBaseVal ∷ BaseType → BaseVal
defaultBaseVal = \case
  UnitT → BulV
  𝔹T    → BoolV null
  ℕT pr → NatV pr null
  ℤT pr → IntV pr null
  𝕊T    → StrV null
  ℙT    → undefined -- TODO
  ℙsT   → undefined -- TODO

defaultVal ∷ Val → IM Val Val
defaultVal ṽ = todoCxt

-- Encrypted

prettyEncrypted ∷ (Pretty a) ⇒ 𝑃 PrinVal → a → Doc
prettyEncrypted ρvs v =
  ppPostF concat levelMODE
  (ppSetBotLevel $ concat
    [ ppPun "{"
    , concat $ inbetween (ppPun ",") $ map pretty $ iter ρvs
    , ppPun "}"
    ]) $
  pretty v

prettyProt ∷ Prot → Doc → Doc
prettyProt φ d =
  ppPostF concat levelMODE
  (ppSetBotLevel $ concat
    [ ppPun "⌈"
    , pretty φ
    , ppPun "⌉"
    ]) $
  d

encCheck ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM Val ()
encCheck ρvsₑ ρvsₐ = guardErr (ρvsₑ ≡ ρvsₐ) $
                     throwIErrorCxt TypeIError "encCheck: ρvsₑ ≢ ρvsₐ" $ frhs
                     [ ("ρvsₑ", pretty ρvsₑ)
                     , ("ρvsₐ", pretty ρvsₐ)
                     ]

-- BoolVal

makePrisms ''BoolVal

instance Pretty BoolVal where
  pretty = \case
    ClearBV v   → pretty v
    EncBV ρvs v → prettyEncrypted ρvs v

instance Null BoolVal where
  null = ClearBV null

elimClearBV ∷ (STACK) ⇒ BoolVal → IM Val 𝔹
elimClearBV = \case
  ClearBV b → return b
  EncBV _ _ → throwIErrorCxt TypeIError "elimClearBV: E" empty𝐿

elimEncBV ∷ (STACK) ⇒ 𝑃 PrinVal → BoolVal → IM Val EncBool
elimEncBV ρvsₑ = \case
  ClearBV _     → throwIErrorCxt TypeIError "elimEncBV: C" empty𝐿
  EncBV ρvsₐ eb → do
    encCheck ρvsₑ ρvsₐ
    return eb

-- EncBool

makePrisms ''EncBool

instance Pretty EncBool where
  pretty eb = case eb of
    GmwB _ → prettyProt GMWP $ ppCon "𝔹"

elimGmwB ∷ EncBool → IM Val GmwBool
elimGmwB eb = error𝑂 (view gmwBL eb) $
                 throwIErrorCxt TypeIError "elimGmwBool: view gmwBL eb ≡ None" $ frhs
                 [ ("eb", pretty eb)
                 ]

-- NatVal

makePrisms ''NatVal

instance Pretty NatVal where
  pretty = \case
    ClearNV v   → pretty v
    EncNV ρvs v → prettyEncrypted ρvs v

instance Null NatVal where
  null = ClearNV null

elimClearNV ∷ (STACK) ⇒ NatVal → IM Val ℕ
elimClearNV = \case
  ClearNV n → return n
  EncNV _ _ → throwIErrorCxt TypeIError "elimClearNV: E" empty𝐿

elimEncNV ∷ (STACK) ⇒ 𝑃 PrinVal → NatVal → IM Val EncNat
elimEncNV ρvsₑ = \case
  ClearNV _     → throwIErrorCxt TypeIError "elimEncNV: C" empty𝐿
  EncNV ρvsₐ en → do
    encCheck ρvsₑ ρvsₐ
    return en

-- EncNat

makePrisms ''EncNat

instance Pretty EncNat where
  pretty en = case en of
    GmwN _ → prettyProt GMWP $ ppCon "ℕ"

elimGmwN ∷ EncNat → IM Val GmwNat
elimGmwN en = error𝑂 (view gmwNL en) $
                throwIErrorCxt TypeIError "elimGmwNat: view gmwNL en ≡ None" $ frhs
                [ ("en", pretty en)
                ]

-- IntVal

makePrisms ''IntVal

instance Pretty IntVal where
  pretty = \case
    ClearZV v   → pretty v
    EncZV ρvs v → prettyEncrypted ρvs v

instance Null IntVal where
  null = ClearZV null

elimClearZV ∷ (STACK) ⇒ IntVal → IM Val ℤ
elimClearZV = \case
  ClearZV n → return n
  EncZV _ _ → throwIErrorCxt TypeIError "elimClearZV: E" empty𝐿

elimEncZV ∷ (STACK) ⇒ 𝑃 PrinVal → IntVal → IM Val EncInt
elimEncZV ρvsₑ = \case
  ClearZV _     → throwIErrorCxt TypeIError "elimEncZV: C" empty𝐿
  EncZV ρvsₐ ez → do
    encCheck ρvsₑ ρvsₐ
    return ez

-- EncInt

makePrisms ''EncInt

instance Pretty EncInt where
  pretty ez = case ez of
    GmwZ _ → prettyProt GMWP $ ppCon "ℤ"

elimGmwZ ∷ EncInt → IM Val GmwInt
elimGmwZ ez = error𝑂 (view gmwZL ez) $
                throwIErrorCxt TypeIError "elimGmwInt: view gmwZL ez ≡ None" $ frhs
                [ ("ez", pretty ez)
                ]

-- IParams

makeLenses ''IParams

makePrettySum ''IParams

θ₀ ∷ 𝕊 → PrinVal → Prg → (PrinVal ⇰ Channel) → (PrinVal ⇰ (Addr ∧ Port)) → IParams
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

iCxtConfigsL ∷ ICxt v ⟢ (PrinVal ⇰ (Addr ∧ Port))
iCxtConfigsL = iParamsConfigsL ⊚ iCxtParamsL

getPrg ∷ (STACK) ⇒ IM Val Prg
getPrg = askL iCxtPrgL

getChannel ∷ (STACK) ⇒ PrinVal → IM Val Channel
getChannel ρv = do
  chans ← askL iCxtChannelsL
  fromSomeCxt $ chans ⋕? ρv

getConfig ∷ (STACK) ⇒ PrinVal → IM Val (Addr ∧ Port)
getConfig ρv = do
  configs ← askL iCxtConfigsL
  fromSomeCxt $ configs ⋕? ρv

getChannels ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (PrinVal ⇰ Channel)
getChannels ρvs = dict ^$ mapM (\ ρv → (ρv ↦) ^$ getChannel ρv) $ iter ρvs

getConfigs ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (PrinVal ⇰ (Addr ∧ Port))
getConfigs ρvs = dict ^$ mapM (\ ρv → (ρv ↦) ^$ getConfig ρv) $ iter ρvs

-- IState

makeLenses ''IState

makePrettySum ''IState

ω₀ ∷ IState v
ω₀ = IState (𝕫64 1) wø dø dø null

getSyncPrg ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (𝑂 Prg)
getSyncPrg ρvs = do
  prgs ← getL iStatePrgsL
  return $ prgs ⋕? ρvs

mkSyncPrg ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val Prg
mkSyncPrg ρvs = do
  prg      ← getPrg
  channels ← list ^$ values ^$ getChannels ρvs
  msb :* lsb ← prgRandSeed prg
  eachOn channels $ \ chan → do
    channelSendStorable chan msb
    channelSendStorable chan lsb
    channelFlush chan
  seeds ← mapMOn channels $ \ chan → do
    msb ← channelRecvStorable @ℕ64 chan
    lsb ← channelRecvStorable @ℕ64 chan
    return $ msb :* lsb
  let sharedSeed = mapBoth sum $ split seeds
  sharedPrg ← prgFromSeed sharedSeed
  modifyL iStatePrgsL ((ρvs ↦ sharedPrg) ⩌!)
  return sharedPrg

getOrMkSyncPrg ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val Prg
getOrMkSyncPrg ρvs = do
  prg𝑂 ← getSyncPrg ρvs
  case prg𝑂 of
    None     → mkSyncPrg ρvs
    Some prg → return prg

getGmw ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val (𝑂 Gmw)
getGmw ρvs = do
  gmws ← getL iStateGmwsL
  return $ gmws ⋕? ρvs

mkGmw ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val Gmw
mkGmw ρvs = do
  me ← askL iCxtMeL
  configs ← getConfigs ρvs
  gmw ← gmwProtocolNew me configs
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

listTL ∷ Type ⌲ Type
listTL = prism constr destr
  where constr τ = ListT τ
        destr = \case
          ListT τ → Some τ
          _ → None

arrTL ∷ Type ⌲ Type
arrTL = prism constr destr
  where constr τ = ArrT τ
        destr = \case
          ArrT τ → Some τ
          _ → None
