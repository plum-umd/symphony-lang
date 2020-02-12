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
  AscrP ψ _τ → bindPatO ψ ṽ
  WildP → return id
  _ → abort

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

wrapInterp ∷ (STACK) ⇒ (ExpR → FailT IM ValP) → Exp → IM ValP
wrapInterp f e = do
  ṽO ← unFailT $ localL iCxtSourceL (Some $ annotatedTag e) $ f $ extract e
  case ṽO of
    Some ṽ → return ṽ
    None → throwIErrorCxt TypeIError "interpExp: failed" $ frhs
      [ ("e",pretty e)
      ]

interpExp ∷ (STACK) ⇒ Exp → IM ValP
interpExp = wrapInterp $ \case
  VarE x → success $ restrictValP *$ interpVar x
  BoolE b → success $ introValP $ BoolV b
  StrE s → success $ introValP $ StrV s
  NatE pr n → success $ introValP $ NatV pr $ trPrNat pr n
  IntE pr i → success $ introValP $ IntV pr $ trPrInt pr i
  FltE pr f → success $ introValP $ FltV pr $ f --trPrFlt pr f (trPrFlt needs to be written)
  BulE → success $ introValP BulV
  IfE e₁ e₂ e₃ → do
    ṽ ← success $ interpExp e₁
    v ← success $ elimValP ṽ
    b ← abort𝑂 $ view boolVL v
    if b
    then success $ interpExp e₂
    else success $ interpExp e₃
  LE e' → success $ do
    ṽ ← interpExp e'
    introValP $ LV ṽ
  RE e' → success $ do
    ṽ ← interpExp e'
    introValP $ RV ṽ
  TupE e₁ e₂ → success $ do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ PairV ṽ₁ ṽ₂
  NilE → success $ introValP NilV
  ConsE e₁ e₂ → success $ do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ ConsV ṽ₁ ṽ₂
  LetTyE _ _ e' → success $ interpExp e'
  LetE ψ e₁ e₂ → success $ do
    ṽ ← interpExp e₁
    bindPat ψ ṽ $ interpExp e₂
  CaseE e' ψes → success $ do
    ṽ ← interpExp e'
    interpCase ṽ ψes
  LamE selfO ψs e' → do
    ξ ← askL iCxtCloL
    ψ :* ψs' ← abort𝑂 $ view unconsL $ ψs
    let e'' = 
          if ψs' ≡ Nil
          then e'
          else siphon e' $ LamE None ψs' e'
    success $ introValP $ CloV selfO ψ e'' ξ
  AppE e₁ e₂ → success $ do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  -- TLamE
  -- TAppE
  SoloE ρes e' → success $ do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    ρṽs ← mapMOn (iter ρvs) $ \ ρv → 
      restrictMode (SecM ρv) $ do
        ṽ ← interpExp e'
        v ← elimValP ṽ
        return $ ρv ↦ v
    return $ ISecVP $ dict ρṽs
  ParE ρes e' → success $ do
    ρvs ← prinExpValss ^$ mapM interpPrinExp ρes
    restrictMode (PSecM ρvs) $ interpExp e'
  ShareE φ ρes e' → do
    ρvs ← success $ prinExpValss ^$ mapM interpPrinExp ρes
    m ← askL iCxtModeL
    guard $ PSecM ρvs ⊑ m
    ṽ ← success $ interpExp e'
    v ← tries
      [ snd ∘ frhs ^$ abort𝑂 $ view sSecVPL ṽ
      , abort𝑂 $ view allVPL ṽ
      ]
    sv ← success $ mpcFrVal v
    return $ ShareVP φ ρvs sv
  AccessE e' ρ → do
    ρv ← success $ interpPrinExpSingle ρ
    ṽ ← success $ interpExp e'
    ρvs ← abort𝑂 $ view iSecVPL ṽ
    v ← abort𝑂 $ view justL $ ρvs ⋕? ρv
    return $ SSecVP (single ρv) v
  BundleE ρes → do
    ISecVP ^$ dict ^$ mapMOn (iter ρes) $ \ (ρ :* e') → do
      ρv ← success $ interpPrinExpSingle ρ
      ṽ ← success $ restrictMode (SecM ρv) $ interpExp e'
      (ρvs,v) ← abort𝑂 $ view sSecVPL ṽ
      guard (ρvs ≡ single ρv)
      return $ ρv ↦ v
  -- BundleUnionE
  RevealE ρes e' → do
    ρvs ← success $ unions ^$ prinExpVals ^^$ mapM interpPrinExp ρes
    ṽ ← success $ interpExp e'
    case ṽ of
      ShareVP _φ _ρs sv →
        let v = valFrMPC sv in
        return $ SSecVP ρvs v
      SSecVP ρs v → do
        guard $ ρs ⊆ ρvs
        return $ SSecVP ρvs v
      _ → throwIErrorCxt TypeIError "interpExp: RevealE: ṽ ∉ {ShareVP _ _ _,SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  -- AscrE
  ReadE τA e' → do
    ṽ ← success $ interpExp e'
    v ← success $ elimValP ṽ
    fn ← abort𝑂 $ view strVL v
    m ← askL iCxtModeL
    tries
      [ do ρ ← abort𝑂 $ view secML m
           v' ← success $ readType ρ τA fn
           return $ SSecVP (single ρ) v'
      -- get rid of this
      , do ρs ← abort𝑂 $ view pSecML m
           ISecVP ^$ dict ^$ mapMOn (iter ρs) $ \ ρ → do
             v' ← success $ readType ρ τA fn
             return $ ρ ↦ v'
      ]
  -- InferE
  -- HoleE
  PrimE o es → success $ do
    ṽs ← mapM interpExp es
    vs :* φρsO ← unShareValPs ṽs
    v ← interpPrim o vs
    reShareValP φρsO v
  TraceE e₁ e₂ → success $ do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  SetE ρes → success $ do
    ρvs ← unions ^$ prinExpVals ^^$ mapM interpPrinExp ρes
    introValP $ PrinSetV ρvs
  _ → abort

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

interpretExample ∷ 𝕊 → IO ValP
interpretExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  o₁ :* σtl ← interpretFile path
  let v = itlStateEnv σtl ⋕! var "main"
  o₂ :* v' ← evalITLMIO σtl $ hijack $ asTLM $ interpApp v $ AllVP BulV
  write ("resources/" ⧺ fn ⧺ ".res") $ "RESOURCE ESTIMATION\n" ⧺ concat (inbetween "\n" $ map show𝕊 $ iOutResEvs $ o₁ ⧺ o₂)
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
  -- testInterpreterExample "cmp"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "euclid"
  -- testInterpreterExample "msort"
  -- testInterpreterExample "pfold"
  -- testInterpreterExample "bind-fp-const"
  -- testInterpreterExample "elim-sec-ls"
  -- testInterpreterExample "cmp-fn-flt"
  -- testInterpreterExample "test"
  -- testInterpreterExample "karmarkar"
  -- testInterpreterExample "atq"
  -- testInterpreterExample "cmp-split"
  -- testInterpreterExample "cmp-tutorial"
  -- testInterpreterExample "add"
