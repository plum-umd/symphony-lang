module PSL.Interpreter where

import UVMHS
import AddToUVMHS

import PSL.Parser
import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Primitives
import PSL.Interpreter.Access
import PSL.Interpreter.PrinExp
import PSL.Interpreter.ReadType
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Json

import qualified Prelude as HS

import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BS

import qualified System.Random as R

import qualified System.FilePath as HS

import qualified System.Console.GetOpt as O

-------------
-- VERSION --
-------------

psli_VERSION ∷ 𝕊
psli_VERSION = "0.1.0.0"

---------------
-- VARIABLES --
---------------

interpVar ∷ (STACK) ⇒ Var → IM ValP
interpVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → return ṽ
    None → throwIErrorCxt SyntaxIError "interpVar: x ∉ dom(γ)" $ frhs
     [ ("x",pretty x)
     , ("dom(γ)",pretty $ keys γ)
     ]

bindVar ∷ (STACK) ⇒ Var → ValP → IM a → IM a
bindVar x ṽ = mapEnvL iCxtEnvL ((x ↦ ṽ) ⩌)

--------------
-- PATTERNS --
--------------

bindPat ∷ (STACK) ⇒ Pat → ValP → IM a → IM a
bindPat ψ ṽ xM = do
  fO ← unFailT $ bindPatO ψ ṽ
  case fO of
    Some f → f xM
    None → throwIErrorCxt TypeIError "bindPat: no matching cases" $ frhs
      [ ("ψ",pretty ψ)
      , ("ṽ",pretty ṽ)
      ]

bindPatO ∷ (STACK) ⇒ Pat → ValP → FailT IM (IM a → IM a)
bindPatO ψ ṽ = case ψ of
  VarP x → return $ bindVar x ṽ
  BulP → return id
  TupP ψ₁ ψ₂ → do
    v ← success $ elimValP ṽ
    (ṽ₁,ṽ₂) ← abort𝑂 $ view pairVL v
    f₁ ← bindPatO ψ₁ ṽ₁ 
    f₂ ← bindPatO ψ₂ ṽ₂
    return $ f₂ ∘ f₁
  LP ψ' → do
    v' ← success $ elimValP ṽ
    ṽ' ← abort𝑂 $ view lVL v'
    bindPatO ψ' ṽ'
  RP ψ' → do
    v' ← success $ elimValP ṽ
    ṽ' ← abort𝑂 $ view rVL v'
    bindPatO ψ' ṽ'
  NilP → do
    v ← success $ elimValP ṽ
    abort𝑂 $ view nilVL v
    return id
  ConsP ψ₁ ψ₂ → do
    v ← success $ elimValP ṽ
    (ṽ₁,ṽ₂) ← abort𝑂 $ view consVL v
    f₁ ← bindPatO ψ₁ ṽ₁ 
    f₂ ← bindPatO ψ₂ ṽ₂
    return $ f₂ ∘ f₁
  EmptyP → do
    ρvs ← abort𝑂 $ view iSecVPL ṽ
    guard $ count ρvs ≡ 0
    return id
  BundleP ρx ψ₁ ψ₂ → do
    ρvs ← abort𝑂 $ view iSecVPL ṽ
    ρ :* v :* ρvs' ← abort𝑂 $ dminView ρvs
    ρv ← success $ introValP $ PrinV $ ValPEV ρ
    let f₁ = bindVar ρx ρv
    f₂ ← bindPatO ψ₁ $ SSecVP (single ρ) v
    f₃ ← bindPatO ψ₂ $ ISecVP ρvs'
    return $ f₃ ∘ f₂ ∘ f₁
  EmptySetP → do
    v ← success $ elimValP ṽ
    guard $ v ≡ PrinSetV pø
    return id
  SetP x ψ' → do
    v ← success $ elimValP ṽ
    ρvs ← abort𝑂 $ view prinSetVL v
    ρ :* ρs ← abort𝑂 $ pmin ρvs
    ρv ← success $ introValP $ PrinV $ ValPEV ρ
    ρvs ← success $ introValP $ PrinSetV ρs
    let f₁ = bindVar x ρv
    f₂ ← bindPatO ψ' ρvs
    return $ f₂ ∘ f₁
  AscrP _ψ _τ → bindPatO ψ ṽ
  WildP → return id

interpCase ∷ (STACK) ⇒ ValP → 𝐿 (Pat ∧ Exp) → IM ValP
interpCase ṽ ψes = do
  fO ← unFailT $ interpCaseO ṽ ψes
  case fO of
    None → throwIErrorCxt TypeIError "interpCase: interpCaseO v ψes = None" $ frhs
      [ ("ṽ",pretty ṽ)
      , ("ψes",pretty ψes)
      ]
    Some ṽ' → return ṽ'

interpCaseO ∷ (STACK) ⇒ ValP → 𝐿 (Pat ∧ Exp) → FailT IM ValP
interpCaseO ṽ ψes = case ψes of
  Nil → abort
  (ψ :* e) :& ψes' → tries
    [ do f ← bindPatO ψ ṽ 
         success $ f $ interpExp e
    , interpCaseO ṽ ψes'
    ]

-----------------
-- APPLICATION --
-----------------

interpApp ∷ (STACK) ⇒ ValP → ValP → IM ValP
interpApp ṽ₁ ṽ₂ = do
  v₁ ← elimValP ṽ₁
  case v₁ of 
    CloV selfO ψ e ξ → do
      let selfγ = case selfO of
            None → id
            Some self → bindVar self ṽ₁
      m <- askL iCxtModeL
      -- we should be able to only capture values, not modes, in closures, and
      -- then `restrictMode m` isn't necessary anymore.
      compose [localL iCxtCloL ξ, restrictMode m, bindPat ψ ṽ₂,selfγ] $ interpExp e
    _ → throwIErrorCxt TypeIError "interpExp: AppE: v₁ ≢ CloV _ _ _ _" $ frhs
      [ ("v₁",pretty v₁)
      ]

-----------------
-- EXPRESSIONS --
-----------------

wrapInterp ∷ (STACK) ⇒ (ExpR → IM ValP) → Exp → IM ValP
wrapInterp f e = localL iCxtSourceL (Some $ annotatedTag e) $ f $ extract e

interpExp ∷ (STACK) ⇒ Exp → IM ValP
interpExp = wrapInterp $ \case
  VarE x → restrictValP *$ interpVar x
  BoolE b → introValP $ BoolV b
  StrE s → introValP $ StrV s
  NatE pr n → introValP $ NatV pr $ trPrNat pr n
  IntE pr i → introValP $ IntV pr $ trPrInt pr i
  FltE pr f → introValP $ FltV pr $ f --trPrFlt pr f (trPrFlt needs to be written)
  BulE → introValP BulV
  IfE e₁ e₂ e₃ → do
    ṽ ← interpExp e₁
    v ← elimValP ṽ
    b ← error𝑂 (view boolVL v) (throwIErrorCxt TypeIError "interpExp: IfE: view boolVL v ≡ None" $ frhs
                                [ ("v",pretty v)
                                ])
    if b
      then interpExp e₂
      else interpExp e₃
  LE e' → do
    ṽ ← interpExp e'
    introValP $ LV ṽ
  RE e' → do
    ṽ ← interpExp e'
    introValP $ RV ṽ
  TupE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ PairV ṽ₁ ṽ₂
  NilE → introValP NilV
  ConsE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ ConsV ṽ₁ ṽ₂
  LetTyE _ _ e' → interpExp e'
  LetE ψ e₁ e₂ → do
    ṽ ← interpExp e₁
    bindPat ψ ṽ $ interpExp e₂
  CaseE e' ψes → do
    ṽ ← interpExp e'
    interpCase ṽ ψes
  LamE selfO ψs e' → do
    ξ ← askL iCxtCloL
    (ψ :* ψs') ← error𝑂 (view unconsL $ ψs) (throwIErrorCxt TypeIError "interpExp: LamE: view unconsL $ ψs ≡ None" $ frhs
                                             [ ("ψs",pretty ψs)
                                             ])
    let e'' = if ψs' ≡ Nil
              then e'
              else siphon e' $ LamE None ψs' e'
      in introValP $ CloV selfO ψ e'' ξ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  -- TLamE
  -- TAppE
  -- SoloE ρes e' → do
  --   ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
  --   ρṽs ← mapMOn (iter ρvs) $ \ ρv → 
  --     restrictMode (SecM ρv) $ do
  --       ṽ ← interpExp e'
  --       v ← elimValP ṽ
  --       return $ ρv ↦ v
  --   return $ ISecVP $ dict ρṽs
  ParE ρes e' → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    if ρvs ≡ pø 
       then return UnknownVP
       else restrictMode (SecM ρvs) $ interpExp e'
  ShareE φ ρes₁ ρes₂ e' → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    m ← askL iCxtModeL
    guardErr (count ρvs₁ ≡ 1) $
      throwIErrorCxt TypeIError "interpExp: ShareE: size ρvs₁ ≠ 1" $ frhs
        [ ("ρvs₁",pretty ρvs₁) ]
    guardErr (SecM ρvs₂ ⊑ m) $ 
      throwIErrorCxt TypeIError "interpExp: ShareE: ρvs₂ ⋢ m" $ frhs
        [ ("ρvs₂",pretty ρvs₂)
        , ("m",pretty m)
        ]
    ṽ ← interpExp e'
    v ← case ṽ of
      SSecVP ρvs v | ρvs₁ ⊆ ρvs → return v
      AllVP v → return v
      _ → throwIErrorCxt TypeIError "interpExp: ShareE: v ∉ {SSecVP _ _,AllVP _}" $ frhs
        [ ("ṽ",pretty ṽ) ]
    tellL iOutResEvsL $ ResEv φ pø ρvs₁ ρvs₂ (getType v) "SHARE" 0 ↦ 1
    sv ← mpcFrVal v
    return $ ShareVP φ ρvs₂ 0 sv
  AccessE e' ρ → do
    ρv ← interpPrinExpSingle ρ
    ṽ ← interpExp e'
    ρvs ← error𝑂 (view iSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: AccessE: view iSecVPL ṽ ≡ None" $ frhs
                                   [ ("ṽ",pretty ṽ)
                                   ])
    v ← error𝑂 (view justL $ ρvs ⋕? ρv) (throwIErrorCxt TypeIError "interpExp: AccessE: ρv not in ρvs" $ frhs
                                         [ ("ρv",pretty ρv)
                                         , ("ρvs",pretty ρvs)
                                         ])
    return $ SSecVP (single ρv) v
  BundleE ρes → do
    ISecVP ^$ dict ^$ mapMOn (iter ρes) $ \ (ρ :* e') → do
      ρv ← interpPrinExpSingle ρ
      ṽ ← restrictMode (SecM $ single ρv) $ interpExp e'
      (ρvs,v) ← error𝑂 (view sSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: BundleE: view sSecVPL ṽ ≡ None" $ frhs
                                         [ ("ṽ",pretty ṽ)
                                         ])
      guardErr (ρvs ≡ single ρv) (throwIErrorCxt TypeIError "interpExp: BundleE: ρvs ≢ single ρv" $ frhs
                                  [ ("ρvs",pretty ρvs)
                                  , ("ρv",pretty ρv)
                                  ])
      return $ ρv ↦ v
  BundleUnionE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    case (ṽ₁,ṽ₂) of
      (ISecVP ρvs₁,ISecVP ρvs₂) → return $ ISecVP $ ρvs₁ ⩌ ρvs₂
      _ → throwIErrorCxt TypeIError "interpExp: BundleUnionE: (ṽ₁,ṽ₂) ≠ (ISecVP _,ISecVP _)" $ frhs
        [ ("ṽ₁",pretty ṽ₁)
        , ("ṽ₂",pretty ṽ₂)
        ]
  RevealE {- ρes₁ -} ρes₂ e' → do
    -- ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    m ← askL iCxtModeL
    case m of
      SecM ρs → guardErr (ρvs₂ ⊆ ρs) $
        throwIErrorCxt TypeIError "interpExp: RevealE: ρvs ⊈ ρs" $ frhs
          [ ("ρvs₂",pretty ρvs₂)
          , ("ρs",pretty ρs)
          ]
      TopM → skip
      _ → (throwIErrorCxt TypeIError "interpExp: RevealE: m ∉ {PSecM _, TopM}" $ frhs
          [ ("m",pretty m)
          ])
    ṽ ← interpExp e'
    case ṽ of
      ShareVP φ ρs md sv {- | ρs ≡ ρvs₁ -} → do
        let v = valFrMPC sv
        tellL iOutResEvsL $ ResEv φ pø ρs ρvs₂ (getTypeMPC sv) "REVEAL" md ↦ 1
        return $ SSecVP ρvs₂ v
      _ → throwIErrorCxt TypeIError "interpExp: RevealE: ṽ ∉ {ShareVP _ _ _,SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  SendE ρes₁ ρes₂ e' → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    guardErr (count ρvs₁ ≡ 1) $
      throwIErrorCxt TypeIError "interpExp: SendE: size ρvs₁ ≠ 1" $ frhs
        [ ("ρvs₁",pretty ρvs₁) ]
    m ← askL iCxtModeL
    case m of
      SecM ρs → guardErr (ρvs₂ ⊆ ρs) $
        throwIErrorCxt TypeIError "interpExp: SendE: ρvs ⊈ ρs" $ frhs
          [ ("ρvs₂",pretty ρvs₂)
          , ("ρs",pretty ρs)
          ]
      TopM → skip
      _ → (throwIErrorCxt TypeIError "interpExp: SendE: m ∉ {PSecM _, TopM}" $ frhs
          [ ("m",pretty m)
          ])
    ṽ ← interpExp e'
    case ṽ of
      SSecVP ρs v | ρvs₁ ⊆ ρs → return $ SSecVP ρvs₂ v
      AllVP v → return $ SSecVP ρvs₂ v
      _ → throwIErrorCxt TypeIError "interpExp: SendE: ṽ ∉ {ShareVP _ _ _,SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  -- AscrE
  ReadE τA e' → do
    ṽ ← interpExp e'
    v ← elimValP ṽ
    m ← askL iCxtModeL
    case (v,m) of
      (StrV fn,SecM ρs) | [ρ] ← tohs $ list ρs → do
        v' ← readType ρ τA fn
        return $ SSecVP (single ρ) v'
      _ → throwIErrorCxt TypeIError "interpExp: ReadE: (v,m) ≠ (StrV _,SecM {_})" $ frhs
        [ ("v",pretty v)
        , ("m",pretty m)
        ]
  RandE τ → do
    wrap :* τ' ← case τ of
      ShareT φ ρes τ' → do
        ρvs ← prinExpValss *$ mapM interpPrinExp ρes
        return $ ShareVP φ ρvs 0 :* τ'
      _ → return $ AllVP ∘ valFrMPC :* τ
    v ← case τ' of
      ℕT ip → io $ NatMV ip ∘ trPrNat ip ∘ nat ^$ R.randomIO @ℕ64
      ℤT ip → io $ IntMV ip ∘ trPrInt ip ∘ int ^$ R.randomIO @ℤ64
      𝔽T fp → io $ FltMV fp ^$ R.randomIO @𝔻
      𝔹T → io $ BoolMV ^$ R.randomIO @𝔹
    return $ wrap v
  RandRangeE τ e → do
    wrap :* τ' ← case τ of
      ShareT φ ρes τ' → do
        ρvs ← prinExpValss *$ mapM interpPrinExp ρes
        return $ ShareVP φ ρvs 0 :* τ'
      _ → return $ AllVP ∘ valFrMPC :* τ
    ṽ ← interpExp e
    v ← elimValP ṽ
    (ṽ₁,ṽ₂) ← 
      elim𝑂 (throwIErrorCxt TypeIError "interpExp: ReadRangeE: Expected a pair argument" $ frhs [ ("v",pretty v) ]) return $
      view pairVL v
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    v' ← case (τ',v₁,v₂) of
      (ℕT ip,NatV ip₁ n₁,NatV ip₂ n₂) | (ip₁ ≡ ip) ⩓ (ip₂ ≡ ip) → io $ NatMV ip ∘ nat ^$ (R.randomRIO @ℕ64) (HS.fromIntegral n₁,HS.fromIntegral n₂)
      (ℤT ip,IntV ip₁ i₁,IntV ip₂ i₂) | (ip₁ ≡ ip) ⩓ (ip₂ ≡ ip) → io $ IntMV ip ∘ int ^$ (R.randomRIO @ℤ64) (HS.fromIntegral i₁,HS.fromIntegral i₂)
      (𝔽T fp,FltV fp₁ d₁,FltV fp₂ d₂) | (fp₁ ≡ fp) ⩓ (fp₂ ≡ fp) → io $ FltMV fp ^$ (R.randomRIO @𝔻) (d₁,d₂)
    return $ wrap v'
  -- InferE
  -- HoleE
  PrimE o es → do
    ṽs ← mapM interpExp es
    vs :* φρsO ← unShareValPs ṽs
    v :* τ ← interpPrim o vs
    let φρsO' = mapOn φρsO $ \ (φ :* ρs :* md) →
          let md' = multDepth φ o + md in
          φ :* ρs :* md'
    v' ← reShareValP φρsO' v
    case φρsO' of
      None → skip
      Some (φ :* ρs :* md) → do
        tellL iOutResEvsL $ ResEv φ ρs pø pø τ o md ↦ 1
    return v'
  TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  SetE ρes → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    introValP $ PrinSetV ρvs
  e → throwIErrorCxt NotImplementedIError "interpExp: not implemented" $ frhs
    [ ("e",pretty e)
    ]

---------------
-- TOP LEVEL --
---------------

interpTL ∷ TL → ITLM ()
interpTL tl = case extract tl of
  DeclTL _ _ → skip
  DefnTL x ψs e →  do
    let e' = buildLambda (annotatedTag tl) x ψs e
    v ← asTLM $ interpExp e'
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL ps → do
    let kinds = dict $ mapOn (iter ps) $ \case
          SinglePD ρ → ρ ↦ SinglePK
          ArrayPD ρ n → ρ ↦ SetPK n
    modifyL itlStateDeclPrinsL (kinds ⩌)
  _ → pptrace (annotatedTag tl) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 TL → ITLM ()
interpTLs = eachWith interpTL

----------
-- MAIN --
----------

-- flagNames ∷ 𝑃 𝕊
-- flagNames = pow
--   [ "resources"
--   ]
-- 
-- paramNames ∷ 𝑃 𝕊
-- paramNames = pow
--   [ "seed"
--   ]

-- parseArgs ∷ 𝐿 𝕊 → 𝕊 ⇰ 𝕊
-- parseArgs = \case 
--   a₁ :& as → case list a₁ of
--     '-' :& '-' :& name | string name ∈ flagNames → 
--       let ps = parseArgs as
--       in (string name ↦ "") ⩌ ps
--     '-' :& '-' :& name | string name ∈ paramNames, a₂ :& as' ← as →
--       let ps = parseArgs as'
--       in (string name ↦ a₂) ⩌ ps
--     -- skip it
--     _ → parseArgs as
--   Nil → dø


data Options = Options
  { optVersion ∷ 𝔹
  , optHelp ∷ 𝔹
  , optDoResources ∷ 𝔹
  , optRandomSeed ∷ 𝑂 ℕ
  } 
  deriving (Eq,Ord,Show)
makeLenses ''Options

options₀ ∷ Options
options₀ = Options
  { optVersion = False
  , optHelp = False
  , optDoResources = False
  , optRandomSeed = None
  }

usageInfoTop ∷ [O.OptDescr (Options → Options)]
usageInfoTop = 
  [ O.Option ['v'] [chars "version"]   
             (O.NoArg $ update optVersionL True)
           $ chars "print version"
  , O.Option ['h'] [chars "help"]
             (O.NoArg $ update optHelpL True)
           $ chars "show help"
  ]

usageInfoRun ∷ [O.OptDescr (Options → Options)]
usageInfoRun = 
  [ O.Option ['r'] [chars "resources"] 
             (O.NoArg $ update optDoResourcesL True) 
           $ chars "enable resource estimation"
  , O.Option ['s'] [chars "seed"]  
             (O.ReqArg (\ s -> update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

initializeIO ∷ Options → IO ()
initializeIO os = exec
  [ case optRandomSeed os of
      None → skip
      Some seed → R.setStdGen $ R.mkStdGen $ HS.fromIntegral seed
  ]

initializeEnv ∷ Options → ITLEnv
initializeEnv os = flip compose γtl₀
  [ if optDoResources os then update itlEnvDoResourcesL True else id
  ]

interpretFile ∷ ITLEnv → ITLState → 𝕊 → IO (ITLState ∧ IOut)
interpretFile γtl σtl path = do
  s ← read path
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  σtl' :* o :* () ← runITLMIO γtl σtl $ eachWith interpTL tls
  return $ σtl' :* o

interpretFileMain ∷ ITLEnv → ITLState → 𝕊 → IO (ValP ∧ 𝑂 ValP)
interpretFileMain γtl σtl path = do
  σtl' :* _ ← interpretFile γtl σtl path
  let main = itlStateEnv σtl' ⋕! var "main"
  o :* v ← evalITLMIO γtl σtl' $ hijack $ asTLM $ interpApp main $ AllVP BulV
  let expectedO = itlStateEnv σtl' ⋕? var "expected"
  let fn = string $ HS.takeBaseName $ chars path
  if itlEnvDoResources γtl
    then BS.writeFile (chars $ "resources/" ⧺ fn ⧺ ".res") $ JSON.encode $ jsonEvents $ iOutResEvs o
    else skip
  return $ v :* expectedO

parseOptions ∷ IO (Options ∧ [𝕊])
parseOptions = do
  as ← askArgs
  let (fs,nos,ems) = O.getOpt O.RequireOrder (usageInfoTop ⧺ usageInfoRun) $ lazyList $ map chars as
  eachOn ems (out ∘ string)
  let os = compose fs options₀
  when (optVersion os) $ \ () → do
    out ""
    out $ "psli version " ⧺ psli_VERSION
  when (optHelp os) $ \ () → do
    out ""
    out "Usage: psli [<command>] [<arguments>] [<target>]"
    out ""
    out $ string $ O.usageInfo (chars "psli [arguments]") usageInfoTop
    out $ string $ O.usageInfo (chars "psli run [arguments] <file>") usageInfoRun
    out $ string $ O.usageInfo (chars "psli example [arguments] <name>")  usageInfoRun
    out $ string $ O.usageInfo (chars "psli test [arguments]") usageInfoRun
  return $ frhs (os,map string nos)

psliMainRun ∷ IO ()
psliMainRun = do
  (os,ts) ← tohs ^$ parseOptions
  fn ← case ts of
    [] → failIO "ERROR: No file specified as target. Correct usage: psli run [<arguments>] <file>"
    [t] → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: psli run [<arguments>] <file>"
  initializeIO os
  let γtl = initializeEnv os
  out ""
  pprint $ ppHorizontal
    [ ppHeader "INTERPRETING FILE:"
    , ppString fn
    ]
  σtl :* _ ← interpretFile γtl σtl₀ "lib/stdlib.psl"
  v ← fst ^$ interpretFileMain γtl σtl fn
  pprint $ ppHeader "RESULT"
  pprint v

psliMainExample ∷ IO ()
psliMainExample = do
  (os,ts) ← tohs ^$ parseOptions
  fn ← case ts of
    [] → failIO "ERROR: No file specified as target. Correct usage: psli example [<arguments>] <name>"
    [t] → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: psli example [<arguments>] <name>"
  initializeIO os
  let γtl = initializeEnv os
  out ""
  pprint $ ppHorizontal 
    [ ppHeader "INTERPRETING EXAMPLE:"
    , ppString fn
    ]
  let path = "examples/" ⧺ fn ⧺ ".psl"
  σtl :* _ ← interpretFile γtl σtl₀ "lib/stdlib.psl"
  v ← fst ^$ interpretFileMain γtl σtl path
  pprint $ ppHeader "RESULT"
  pprint v

psliMainTest ∷ IO ()
psliMainTest = do
  (os,ts) ← tohs ^$ parseOptions
  case ts of
    [] → skip
    _ → failIO "ERROR: Command does not accept targets. Correct usage: psli test [<arguments>]"
  let γtl = initializeEnv os
  out ""
  pprint $ ppHeader "TESTING INTERPRETER"
  σtl :* _ ← interpretFile γtl σtl₀ "lib/stdlib.psl"
  indir "tests" $ do
    fns ← files
    vevs ← mapMOn fns $ \ fn → do
      initializeIO os
      (fn :*) ^$ interpretFileMain γtl σtl fn
    pprint $ ppVertical
      [ ppHeader "TESTS"
      , concat
        [ ppSpace $ 𝕟64 2
        , ppAlign $ ppVertical $ mapOn vevs $ \ (fn :* (v :* ev)) → case Some v ≡ ev of
            True → ppHorizontal 
              [ ppFormat (formats [FG darkGreen]) $ ppString "PASSED"
              , ppString fn
              ]
            False → ppVertical
              [ ppHorizontal 
                  [ ppFormat (formats [FG darkRed]) $ ppString "FAILED"
                  , ppString fn
                  ]
              , concat
                  [ ppSpace $ 𝕟64 2
                  , ppAlign $ ppVertical
                      [ ppHorizontal [ppHeader "RETURNED:",pretty v]
                      , ppHorizontal [ppHeader "EXPECTED:",pretty ev]
                      ]
                  ]
              ]
        ]
      ]
<<<<<<< HEAD
  -- testInterpreterExample "add"
  -- testInterpreterExample "arg-par-contains"
  -- testInterpreterExample "atq"
  -- testInterpreterExample "bind-fp-const"
  -- testInterpreterExample "bind-shares"
  -- testInterpreterExample "cmp"
  -- testInterpreterExample "cmp-fn-flt"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "elim-sec-ls"
  -- testInterpreterExample "empty-par-diverge"
  -- testInterpreterExample "euclid"
  -- testInterpreterExample "indy-pars"
  -- testInterpreterExample "pfold"
  -- testInterpreterExample "karmarkar-simple"
  -- testInterpreterExample "karmarkar-silly"
  -- testInterpreterExample "msort"
  -- testInterpreterExample "partial-diverge"
  -- testInterpreterExample "reshare"
  -- testInterpreterExample "share-ls"
  -- testInterpreterExample "single-share"
  -- testInterpreterExample "ssec-other-ssec"
  -- testInterpreterExample "ssec-shr"
  -- testInterpreterExample "sumprod"
  -- testInterpreterExample "test"
  -- testInterpreterExample "uninspecting-par"
  -- testInterpreterExample "rand"
=======

pslMainInfo ∷ IO ()
pslMainInfo = do
  out ""
  out $ concat $ inbetween "\n" 
    [ "psli is the interpreter for the PSL language developed by"
    , "the PANTHEON team, funded by IARPA for the HECTOR project."
    ]
  (_,ts) ← tohs ^$ parseOptions
  case ts of
    [] → skip
    _ → failIO "ERROR: Command does not accept targets. Correct usage: psli [<arguments>]"

interpreterMain ∷ IO ()
interpreterMain = do
  map list args ≫= \case
    "run" :& as → localArgs as $ psliMainRun
    "example" :& as → localArgs as $ psliMainExample
    "test" :& as → localArgs as psliMainTest
    Nil → localArgs (list ["--version","--help"]) pslMainInfo
    as → localArgs as pslMainInfo
>>>>>>> 8d097175cce5b25684ea94ac66940a1a10e606d3
