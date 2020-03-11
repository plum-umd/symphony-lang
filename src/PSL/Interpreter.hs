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

import qualified Prelude as HS

import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BS

import qualified System.Random as R

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
    let f₁ = bindVar ρx $ AllVP $ PrinV $ ValPEV ρ
    f₂ ← bindPatO ψ₁ $ SSecVP (single ρ) v
    f₃ ← bindPatO ψ₂ $ ISecVP ρvs'
    return $ f₃ ∘ f₂ ∘ f₁
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
      compose [localL iCxtCloL ξ, restrictMode m,bindPat ψ ṽ₂,selfγ] $ interpExp e
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
  SoloE ρes e' → do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    ρṽs ← mapMOn (iter ρvs) $ \ ρv → 
      restrictMode (SecM ρv) $ do
        ṽ ← interpExp e'
        v ← elimValP ṽ
        return $ ρv ↦ v
    return $ ISecVP $ dict ρṽs
  ParE ρes e' → do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    restrictMode (PSecM ρvs) $ interpExp e'
  ShareE φ ρes e' → do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    m ← askL iCxtModeL
    guardErr (PSecM ρvs ⊑ m) (throwIErrorCxt TypeIError "interpExp: ShareE: ρvs ⋢ m" $ frhs
                              [ ("ρvs",pretty ρvs)
                              , ("m",pretty m)
                              ])
    ṽ ← interpExp e'
    v ← error𝑂 (tries
                [ snd ∘ frhs ^$ abort𝑂 $ view sSecVPL ṽ
                , abort𝑂 $ view allVPL ṽ
                ])
        (throwIErrorCxt TypeIError "interpExp: ShareE: failed" $ frhs
         [ ("ṽ",pretty ṽ)
         ])
    sv ← mpcFrVal v
    return $ ShareVP φ ρvs 0 sv
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
      ṽ ← restrictMode (SecM ρv) $ interpExp e'
      (ρvs,v) ← error𝑂 (view sSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: BundleE: view sSecVPL ṽ ≡ None" $ frhs
                                         [ ("ṽ",pretty ṽ)
                                         ])
      guardErr (ρvs ≡ single ρv) (throwIErrorCxt TypeIError "interpExp: BundleE: ρvs ≢ single ρv" $ frhs
                                  [ ("ρvs",pretty ρvs)
                                  , ("ρv",pretty ρv)
                                  ])
      return $ ρv ↦ v
  -- BundleUnionE
  RevealE ρes e' → do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    m ← askL iCxtModeL
    case m of
      PSecM ρs → guardErr (ρvs ⊆ ρs) (throwIErrorCxt TypeIError "interpExp: RevealE: ρvs ⊈ ρs" $ frhs
                                      [ ("ρvs",pretty ρvs)
                                      , ("ρs",pretty ρs)
                                      ])
      TopM → skip
      _ → (throwIErrorCxt TypeIError "interpExp: RevealE: m ∉ {PSecM _, TopM}" $ frhs
          [ ("m",pretty m)
          ])
    ṽ ← interpExp e'
    case ṽ of
      ShareVP _φ _ρs _md sv →
        let v = valFrMPC sv in
        return $ SSecVP ρvs v
      SSecVP _ρs v → return $ SSecVP ρvs v
      _ → throwIErrorCxt TypeIError "interpExp: RevealE: ṽ ∉ {ShareVP _ _ _,SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  -- AscrE
  ReadE τA e' → do
    ṽ ← interpExp e'
    v ← elimValP ṽ
    case view strVL v of
      Some fn → do
        m ← askL iCxtModeL
        case view secML m of
          Some ρ → do
            v' ← readType ρ τA fn
            return $ SSecVP (single ρ) v'
          None → do -- get rid of this ↓
            case view pSecML m of
              Some ρs →
                ISecVP ^$ dict ^$ mapMOn (iter ρs) $ \ ρ → do
                v' ← readType ρ τA fn
                return $ ρ ↦ v' --    ↑
              None → throwIErrorCxt TypeIError "interpExp: ReadE: Could not read" $ frhs
                [ ("m",pretty m)
                ]
      None → throwIErrorCxt TypeIError "interpExp: ReadE: view strVL v ≡ None" $ frhs
        [ ("v",pretty v)
        ]

  RandE τ → do
    wrap :* τ' ← case τ of
      ShareT φ ρes τ' → do
        ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
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
        ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
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
          let md' = if o ≡ "TIMES" then md + 1 else md
          in φ :* ρs :* md'
    v' ← reShareValP φρsO' v
    case φρsO' of
      None → skip
      Some (φ :* ρs :* md) → do 
        tellL iOutResEvsL $ single $ ResEv φ ρs τ o md
    return v'
  TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  SetE ρes → do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
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

-------------
-- TESTING --
-------------

interpretFile ∷ 𝕊 → IO (IOut ∧ ITLState )
interpretFile fn = do
  s ← read fn
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  evalITLMIO σtl₀ $ do
    o ← retOut $ interpTLs tls
    σ ← get
    return $ o :* σ

stringProtocol ∷ Prot → 𝕊
stringProtocol = \case
  YaoP  → "yao"
  BGWP  → "bgw"
  GMWP  → "gmw"
  BGVP  → "bgv"
  SPDZP → "spdz"

jsonPrinVal ∷ PrinVal → 𝕊
jsonPrinVal = \case
  SinglePV s → s
  AccessPV s i → s ⧺ "_" ⧺ show𝕊 i

jsonPrins ∷ 𝑃 PrinVal → JSON.Value
jsonPrins = JSON.toJSON ∘ lazyList ∘ map jsonPrinVal ∘ iter

jsonEvent ∷ ResEv → JSON.Value
jsonEvent (ResEv φ ρs τ o md) = 
  JSON.object [ "protocol" JSON..= stringProtocol φ 
              , "principals" JSON..= jsonPrins ρs
              , "type" JSON..= τ
              , "op" JSON..= o
              , "mult_depth" JSON..= md
              ]

jsonEvents ∷ (ToIter ResEv t) ⇒ t → JSON.Value
jsonEvents = JSON.toJSON ∘ lazyList ∘ map jsonEvent ∘ iter

interpretExample ∷ 𝕊 → IO ValP
interpretExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  o₁ :* σtl ← interpretFile path
  let v = itlStateEnv σtl ⋕! var "main"
  o₂ :* v' ← evalITLMIO σtl $ hijack $ asTLM $ interpApp v $ AllVP BulV
  let o = o₁ ⧺ o₂
  -- write ("resources/" ⧺ fn ⧺ ".res") $ "RESOURCE ESTIMATION\n" ⧺ concat (inbetween "\n" $ map show𝕊 $ iOutResEvs o)
  BS.writeFile (chars $ "resources/" ⧺ fn ⧺ ".res") $ JSON.encode $ jsonEvents $ iOutResEvs o
  return v'

interpretTest ∷ 𝕊 → IO (ValP ∧ ValP)
interpretTest fn = do
  _ :* σtl ← interpretFile fn
  let v = itlStateEnv σtl ⋕! var "main"
      ev = itlStateEnv σtl ⋕! var "expected"
  v' ← evalITLMIO σtl $ asTLM $ interpApp v $ AllVP BulV
  return $ v' :* ev

testInterpreterExample ∷ 𝕊 → IO ()
testInterpreterExample fn = pprint *$ interpretExample fn

testInterpreter ∷ IO ()
testInterpreter = do
  -- UNCOMMENT TO FIX THE RANDOM SEED
  -- R.setStdGen $ R.mkStdGen $ HS.fromIntegral 54321
  pprint $ ppHeader "TESTING INTERPRETER"
  indir "tests" $ do
    fs ← files
    pprint $ ppVertical
      [ ppHeader "TESTS"
      , concat
        [ ppSpace $ 𝕟64 2
        , ppAlign $ ppVertical $ mapOn fs $ \ fn →
            let v :* ev = ioUNSAFE $ interpretTest fn
            in case v ≡ ev of
              True → ppHorizontal [ppFormat (formats [FG darkGreen]) $ ppString "PASSED",ppString fn]
              False → ppVertical
                [ ppHorizontal [ppFormat (formats [FG darkRed]) $ ppString "FAILED",ppString fn]
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
  testInterpreterExample "karmarkar-silly"
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
