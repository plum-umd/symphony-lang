module PSL.Interpreter where

import UVMHS
import AddToUVMHS

import PSL.Config
import PSL.Parser
import PSL.Syntax

import PSL.Interpreter.Access
import PSL.Interpreter.Json
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Primitives
import PSL.Interpreter.PrinExp
import PSL.Interpreter.ReadType
import PSL.Interpreter.Truncating
import PSL.Interpreter.Types

import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BS
import qualified Prelude as HS
import qualified System.Console.GetOpt as O
import qualified System.FilePath as HS
import qualified System.Random as R

-------------
-- VERSION --
-------------


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
    v ← lift $ elimValP ṽ
    ṽ₁ :* ṽ₂ ← abort𝑂 $ view pairVL v
    f₁ ← bindPatO ψ₁ ṽ₁ 
    f₂ ← bindPatO ψ₂ ṽ₂
    return $ f₂ ∘ f₁
  LP ψ' → do
    v' ← lift $ elimValP ṽ
    ṽ' ← abort𝑂 $ view lVL v'
    bindPatO ψ' ṽ'
  RP ψ' → do
    v' ← lift $ elimValP ṽ
    ṽ' ← abort𝑂 $ view rVL v'
    bindPatO ψ' ṽ'
  NilP → do
    v ← lift $ elimValP ṽ
    abort𝑂 $ view nilVL v
    return id
  ConsP ψ₁ ψ₂ → do
    v ← lift $ elimValP ṽ
    ṽ₁ :* ṽ₂ ← abort𝑂 $ view consVL v
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
    ρv ← lift $ introValP $ PrinV $ ValPEV ρ
    let f₁ = bindVar ρx ρv
    f₂ ← bindPatO ψ₁ $ SSecVP (single ρ) v
    f₃ ← bindPatO ψ₂ $ ISecVP ρvs'
    return $ f₃ ∘ f₂ ∘ f₁
  EmptySetP → do
    v ← lift $ elimValP ṽ
    guard $ v ≡ PrinSetV pø
    return id
  SetP x ψ' → do
    v ← lift $ elimValP ṽ
    ρvs ← abort𝑂 $ view prinSetVL v
    ρ :* ρs ← abort𝑂 $ pmin ρvs
    ρv ← lift $ introValP $ PrinV $ ValPEV ρ
    ρvs' ← lift $ introValP $ PrinSetV ρs
    let f₁ = bindVar x ρv
    f₂ ← bindPatO ψ' ρvs'
    return $ f₂ ∘ f₁
  AscrP ψ' _τ → bindPatO ψ' ṽ
  WildP → return id

data MatchState = NoMatch | LeftMatch | RightMatch

bindPatMPC ∷ (STACK) ⇒ ShareInfo → Pat → ValMPC → 𝑂 (IM (ShareInfo ∧ ValMPC) → IM (ShareInfo ∧ ValMPC))
bindPatMPC si ψ vmpc = case ψ of
  VarP x → return $ \ xM → do
    ṽ ← reShareValP vmpc si
    si' :* vmpc' ← bindVar x ṽ xM
    si'' ← joinShareInfo si si'
    return $ si'' :* vmpc'
  TupP ψ₁ ψ₂ → do
    vmpc₁ :* vmpc₂ ← view pairMVL vmpc
    f₁ ← bindPatMPC si ψ₁ vmpc₁
    f₂ ← bindPatMPC si ψ₂ vmpc₂
    return $ \ xM → do
      si' :* vmpc' ← compose [f₁,f₂] xM
      si'' ← joinShareInfo si si'
      return $ si'' :* vmpc'
  LP ψ' → do 
    md :* b :* vmpc₁ :* _vmpc₂ ← view sumMVL vmpc
    f ← bindPatMPC si ψ' vmpc₁
    return $ \ xM → do
      si' :* vmpc' ← mapEnvL iCxtMPCPathConditionL ((md :* b :* si) :&) $ f xM
      vmpc'' ← muxMPCVal md si b vmpc' DefaultMV
      si'' ← joinShareInfo si si'
      return $ si'' :* vmpc''
  RP ψ' → do
    md :* b :* _vmpc₁ :* vmpc₂ ← view sumMVL vmpc
    f ← bindPatMPC si ψ' vmpc₂
    return $ \ xM → do
      si' :* vmpc' ← mapEnvL iCxtMPCPathConditionL ((md :* not b :* si) :&) $ f xM
      vmpc'' ← muxMPCVal md si b DefaultMV vmpc'
      si'' ← joinShareInfo si si'
      return $ si'' :* vmpc''
  BulP → do
    view bulMVL vmpc
    return id
  _ → error "TODO: not implemented"

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
         lift $ f $ interpExp e
    , interpCaseO ṽ ψes'
    ]

-----------------
-- APPLICATION --
-----------------

interpApp ∷ (STACK) ⇒ ValP → ValP → IM ValP
interpApp ṽ₁ ṽ₂ = do
  v₁ ← elimValP ṽ₁
  case v₁ of 
    CloV selfO ψ e γ → do
      let selfγ = case selfO of
            None → id
            Some self → bindVar self ṽ₁
      compose [localL iCxtEnvL γ,bindPat ψ ṽ₂,selfγ] $ interpExp e
    _ → throwIErrorCxt TypeIError "interpExp: AppE: v₁ ≢ CloV _ _ _ _" $ frhs
      [ ("v₁",pretty v₁)
      ]

-----------------
-- EXPRESSIONS --
-----------------

wrapInterp ∷ (STACK) ⇒ (ExpR → IM ValP) → Exp → IM ValP
wrapInterp f e = localL iCxtSourceL (Some $ annotatedTag e) $ f $ extract e

reportPrimop ∷ (STACK) ⇒ 𝕊 → 𝕊 → 𝕊 → ℕ → ShareInfo → IM ()
reportPrimop τ₁ τ₂ op md = \case
  NotShared → skip
  Shared zk φ ρs → do
    let τ :* τf :* τt =
          if τ₂ ≡ null 
          then τ₁ :* null :* null
          else null :* τ₁ :* τ₂
    tellL iOutResEvsL $ ResEv zk φ ρs pø pø τ τf τt op md ↦ 1

interpReportPrim ∷ Op → ℕ → ShareInfo → 𝐿 BaseValMPC → IM (ℕ ∧ BaseValMPC)
interpReportPrim op md si vmpcs = do
  τ₁ :* τ₂ :* vmpc ← interpPrim op vmpcs
  reportPrimop τ₁ τ₂ (opName op) md si
  return $ (md + multDepthShareInfo op si) :* vmpc

defaultBaseVal ∷ (STACK) ⇒ BaseValMPC → BaseValMPC
defaultBaseVal = \case
  BoolMV _ → BoolMV False
  NatMV p _ → NatMV p zero
  IntMV p _ → IntMV p zero
  FltMV p _ → FltMV p zero
  PrinMV _ → PrinMV BotBTD

sumMPCVal ∷ (STACK) ⇒ ShareInfo → ValMPC → ValMPC → IM ValMPC
sumMPCVal si vmpc₁ vmpc₂ = case (vmpc₁,vmpc₂) of
  (DefaultMV,DefaultMV) → return DefaultMV
  (BaseMV md₁ bvmpc₁,BaseMV md₂ bvmpc₂) → do
    let md = md₁ ⊔ md₂
    md' :* vmpc ← interpReportPrim PlusO md si $ list [bvmpc₁,bvmpc₂]
    return $ BaseMV md' vmpc
  (BaseMV md₁ bvmpc₁,DefaultMV) → do
    let bvmpc₂ = defaultBaseVal bvmpc₁
    md' :* vmpc ← interpReportPrim PlusO md₁ si $ list [bvmpc₁,bvmpc₂]
    return $ BaseMV md' vmpc
  (DefaultMV,BaseMV md₂ bvmpc₂) → do
    let bvmpc₁ = defaultBaseVal bvmpc₁
    md' :* vmpc ← interpReportPrim PlusO md₂ si $ list [bvmpc₁,bvmpc₂]
    return $ BaseMV md' vmpc
  (PairMV vmpc₁₁ vmpc₁₂,PairMV vmpc₂₁ vmpc₂₂) → do
    vmpc₁' ← sumMPCVal si vmpc₁₁ vmpc₂₁
    vmpc₂' ← sumMPCVal si vmpc₁₂ vmpc₂₂
    return $ PairMV vmpc₁' vmpc₂'
  (PairMV vmpc₁₁ vmpc₁₂,DefaultMV) → do
    vmpc₁' ← sumMPCVal si vmpc₁₁ DefaultMV
    vmpc₂' ← sumMPCVal si vmpc₁₂ DefaultMV
    return $ PairMV vmpc₁' vmpc₂'
  (DefaultMV,PairMV vmpc₂₁ vmpc₂₂) → do
    vmpc₁' ← sumMPCVal si DefaultMV vmpc₂₁
    vmpc₂' ← sumMPCVal si DefaultMV vmpc₂₂
    return $ PairMV vmpc₁' vmpc₂'
  (SumMV md₁ b₁ mvpc₁₁ mvpc₁₂,SumMV md₂ b₂ mvpc₂₁ mvpc₂₂) → do
    let md = md₁ ⊔ md₂
    md₁' :* bvmpc ← interpReportPrim OrO md si $ list [BoolMV b₁,BoolMV b₂]
    b₁' ← error𝑂 (view boolMVL bvmpc) $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← sumMPCVal si mvpc₁₁ mvpc₂₁
    vmpc₂' ← sumMPCVal si mvpc₁₂ mvpc₂₂
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (SumMV md₁ b₁ mvpc₁₁ mvpc₁₂,DefaultMV) → do
    let md = md₁
    md₁' :* bvmpc ← interpReportPrim OrO md si $ list [BoolMV b₁,BoolMV False]
    b₁' ← error𝑂 (view boolMVL bvmpc) $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← sumMPCVal si mvpc₁₁ DefaultMV
    vmpc₂' ← sumMPCVal si mvpc₁₂ DefaultMV
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (DefaultMV,SumMV md₂ b₂ mvpc₂₁ mvpc₂₂) → do
    let md = md₂
    md₁' :* bvmpc ← interpReportPrim OrO md si $ list [BoolMV False,BoolMV b₂]
    b₁' ← error𝑂 (view boolMVL bvmpc) $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← sumMPCVal si DefaultMV mvpc₂₁
    vmpc₂' ← sumMPCVal si DefaultMV mvpc₂₂
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (BulMV,BulMV) → return $ BulMV
  (BulMV,DefaultMV) → return $ BulMV
  (DefaultMV,BulMV) → return $ BulMV
  _ → throwIErrorCxt TypeIError "sumMPCVal: not implemented" $ frhs
    [ ("vmpc₁",pretty vmpc₁)
    , ("vmpc₂",pretty vmpc₂)
    ]

muxMPCVal ∷ (STACK) ⇒ ℕ → ShareInfo → 𝔹 → ValMPC → ValMPC → IM ValMPC
muxMPCVal md₁ si b₁ vmpc₂ vmpc₃ = case (vmpc₂, vmpc₃) of
  (DefaultMV,DefaultMV) → return DefaultMV
  (BaseMV md₂ bvmpc₂,BaseMV md₃ bvmpc₃) → do
    let md = md₁ ⊔ md₂ ⊔ md₃
    md' :* vmpc ← interpReportPrim CondO md si $ list [BoolMV b₁,bvmpc₂,bvmpc₃]
    return $ BaseMV md' vmpc
  (BaseMV md₂ bvmpc₂,DefaultMV) → do
    let bvmpc₃ = defaultBaseVal bvmpc₂
    let md = md₁ ⊔ md₂
    md' :* vmpc ← interpReportPrim CondO md si $ list [BoolMV b₁,bvmpc₂,bvmpc₃]
    return $ BaseMV md' vmpc
  (DefaultMV,BaseMV md₃ bvmpc₃) → do
    let bvmpc₂ = defaultBaseVal bvmpc₃
    let md = md₁ ⊔ md₃
    md' :* vmpc ← interpReportPrim CondO md si $ list [BoolMV b₁,bvmpc₂,bvmpc₃]
    return $ BaseMV md' vmpc
  (PairMV vmpc₂₁ vmpc₂₂,PairMV vmpc₃₁ vmpc₃₂) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₁ vmpc₃₁
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₂ vmpc₃₂
    return $ PairMV vmpc₁' vmpc₂'
  (PairMV vmpc₂₁ vmpc₂₂,DefaultMV) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₁ DefaultMV
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₂ DefaultMV
    return $ PairMV vmpc₁' vmpc₂'
  (DefaultMV,PairMV vmpc₃₁ vmpc₃₂) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₁
    vmpc₂' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₂
    return $ PairMV vmpc₁' vmpc₂'
  (SumMV md₂ b₂ vmpc₂₂ vmpc₂₃,SumMV md₃ b₃ vmpc₃₂ vmpc₃₃) → do
    let md = md₁ ⊔ md₂ ⊔ md₃
    md₁' :* bvmpc₁' ← interpReportPrim CondO md si $ list [BoolMV b₁,BoolMV b₂,BoolMV b₃]
    b₁' ← error𝑂 (view boolMVL bvmpc₁') $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₂ vmpc₃₂
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₃ vmpc₃₃
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (SumMV md₂ b₂ vmpc₂₂ vmpc₂₃,DefaultMV) → do
    let md = md₁ ⊔ md₂
    md₁' :* bvmpc₁' ← interpReportPrim CondO md si $ list [BoolMV b₁,BoolMV b₂,BoolMV False]
    b₁' ← error𝑂 (view boolMVL bvmpc₁') $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₂ DefaultMV
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₃ DefaultMV
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (DefaultMV,SumMV md₃ b₃ vmpc₃₂ vmpc₃₃) → do
    let md = md₁ ⊔ md₃
    md₁' :* bvmpc₁' ← interpReportPrim CondO md si $ list [BoolMV b₁,BoolMV False,BoolMV b₃]
    b₁' ← error𝑂 (view boolMVL bvmpc₁') $ throwIErrorCxt InternalIError "bad" null
    vmpc₁' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₂
    vmpc₂' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₃
    return $ SumMV md₁' b₁' vmpc₁' vmpc₂'
  (NilMV,NilMV) → return NilMV
  (NilMV,DefaultMV) → return NilMV
  (DefaultMV,NilMV) → return NilMV
  (ConsMV vmpc₂₁ vmpc₂₂,ConsMV vmpc₃₁ vmpc₃₂) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₁ vmpc₃₁
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₂ vmpc₃₂
    return $ ConsMV vmpc₁' vmpc₂'
  (ConsMV vmpc₂₁ vmpc₂₂,DefaultMV) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ vmpc₂₁ DefaultMV
    vmpc₂' ← muxMPCVal md₁ si b₁ vmpc₂₂ DefaultMV
    return $ ConsMV vmpc₁' vmpc₂'
  (DefaultMV,ConsMV vmpc₃₁ vmpc₃₂) → do
    vmpc₁' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₁
    vmpc₂' ← muxMPCVal md₁ si b₁ DefaultMV vmpc₃₂
    return $ ConsMV vmpc₁' vmpc₂'
  (BulMV,BulMV) → return $ BulMV
  (BulMV,DefaultMV) → return $ BulMV
  (DefaultMV,BulMV) → return $ BulMV
  _ → throwIErrorCxt TypeIError "muxMPCVal: not implemented" $ frhs
    [ ("vmpc₂",pretty vmpc₂)
    , ("vmpc₃",pretty vmpc₃)
    ]

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
  MuxIfE e₁ e₂ e₃ → do
    ṽ₁ ← interpExp e₁
    si₁ :* vmpc₁ ← unShareValP ṽ₁
    md₁ :* bvmpc₁ ← error𝑂 (view baseMVL vmpc₁) $ 
      throwIErrorCxt TypeIError "interpExp: MuxIfE: vmpc₁ ≠ BaseMV _ _" $ frhs
        [ ("vmpc₁",pretty vmpc₁) ]
    b₁ ← error𝑂 (view boolMVL bvmpc₁) $ throwIErrorCxt TypeIError "bad" null
    ṽ₂ ← mapEnvL iCxtMPCPathConditionL ((md₁:* b₁ :* si₁) :&) $ do
      interpExp e₂
    ṽ₃ ← mapEnvL iCxtMPCPathConditionL ((md₁:* not b₁ :* si₁) :&) $ do
      interpExp e₃
    si₂ :* vmpc₂ ← unShareValP ṽ₂
    si₃ :* vmpc₃ ← unShareValP ṽ₃
    si ← joinShareInfos [si₁,si₂,si₃]
    vmpc' ← muxMPCVal md₁ si b₁ vmpc₂ vmpc₃
    reShareValP vmpc' si
  LE e → do
    ṽ ← interpExp e
    introValP $ LV ṽ
  RE e → do
    ṽ ← interpExp e
    introValP $ RV ṽ
  TupE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    return $ PairVP ṽ₁ ṽ₂
  NilE → introValP NilV
  ConsE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    introValP $ ConsV ṽ₁ ṽ₂
  LetTyE _ e → interpExp e
  LetE ψ e₁ e₂ → do
    ṽ ← interpExp e₁
    bindPat ψ ṽ $ interpExp e₂
  CaseE e ψes → do
    ṽ ← interpExp e
    interpCase ṽ ψes
  MuxCaseE e ψes → do
    ṽ ← interpExp e
    si :* vmpc ← unShareValP ṽ
    sivmpcs ← concat ^$ mapMOn ψes $ \ (ψ :* e') → do
      case bindPatMPC si ψ vmpc of
        None → return $ list []
        Some f → single ^$ f $ do
          ṽ' ← interpExp e'
          unShareValP ṽ'
    si' :* vmpc' ← mfoldOnFrom sivmpcs (NotShared :* DefaultMV) $ \ (si₁ :* vmpc₁) (si₂ :* vmpc₂) → do
      si'' ← joinShareInfo si₁ si₂
      (:*) si'' ^$ sumMPCVal si'' vmpc₁ vmpc₂
    reShareValP vmpc' si'
  LamE selfO ψs e → do
    γ ← askL iCxtEnvL
    (ψ :* ψs') ← error𝑂 (view unconsL $ ψs) (throwIErrorCxt TypeIError "interpExp: LamE: view unconsL $ ψs ≡ None" $ frhs
                                             [ ("ψs",pretty ψs)
                                             ])
    let e' = if ψs' ≡ Nil
              then e
              else siphon e $ LamE None ψs' e
      in introValP $ CloV selfO ψ e' γ
  AppE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    interpApp ṽ₁ ṽ₂
  ParE ρes e → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    if ρvs ≡ pø 
       then return UnknownVP
       else restrictMode (SecM ρvs) $ interpExp e
  ShareE φ ρes₁ ρes₂ e → do
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
    ṽ ← interpExp e
    sv ← restrictMode (SecM ρvs₁) $ do
      v ← elimValP ṽ
      mpcFrValF v $ \ bv → do
        tellL iOutResEvsL $ ResEv False φ pø ρvs₁ ρvs₂ (getTypeBaseMPC bv) null null "SHARE" 0 ↦ 1
    reShareValPShared False φ ρvs₂ sv 
  AccessE e ρ → do
    ρv ← interpPrinExpSingle ρ
    ṽ ← interpExp e
    ρvs ← error𝑂 (view iSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: AccessE: view iSecVPL ṽ ≡ None" $ frhs
                                   [ ("ṽ",pretty ṽ)
                                   ])
    v ← error𝑂 (view justL $ ρvs ⋕? ρv) (throwIErrorCxt TypeIError "interpExp: AccessE: ρv not in ρvs" $ frhs
                                         [ ("ρv",pretty ρv)
                                         , ("ρvs",pretty ρvs)
                                         ])
    return $ SSecVP (single ρv) v
  BundleE ρes → do
    ISecVP ^$ dict ^$ mapMOn (iter ρes) $ \ (ρ :* e) → do
      ρv ← interpPrinExpSingle ρ
      ṽ ← restrictMode (SecM $ single ρv) $ interpExp e
      ρvs :* v ← error𝑂 (view sSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: BundleE: view sSecVPL ṽ ≡ None" $ frhs
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
  RevealE ρes₂ e → do
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    m ← askL iCxtModeL
    case m of
      SecM ρs → guardErr (ρvs₂ ⊆ ρs) $
        throwIErrorCxt TypeIError "interpExp: RevealE: ρvs ⊈ ρs" $ frhs
          [ ("ρvs₂",pretty ρvs₂)
          , ("ρs",pretty ρs)
          ]
      TopM → skip
    ṽ ← interpExp e
    revealValP False ρvs₂ ṽ
  SendE ρes₁ ρes₂ e → do
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
    ṽ ← interpExp e
    case ṽ of
      SSecVP ρs v | ρvs₁ ⊆ ρs → return $ SSecVP ρvs₂ v
      AllVP v → return $ SSecVP ρvs₂ v
      _ → throwIErrorCxt TypeIError "interpExp: SendE: ṽ ∉ {ShareVP _ _ _,SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
  -- AscrE
  ReadE τA e → do
    ṽ ← interpExp e
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
  WriteE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    m ← askL iCxtModeL
    case (m,v₂) of
      (SecM ρs,StrV fn) | [ρ] ← tohs $ list ρs → do
        writeVal ρ v₁ fn
        introValP $ BulV
      _ → throwIErrorCxt TypeIError "interpExp: WriteE: m ≠ SecM {ρ}" null
  RandE τ → do
    wrap :* τ' ← case τ of
      ShareT φ ρes τ' → do
        ρvs ← prinExpValss *$ mapM interpPrinExp ρes
        return $ (ShareVP False φ ρvs ^∘ mpcFrVal) :* τ'
      _ → return $ introValP :* τ
    v ← case τ' of
      ℕT ip → io $ NatV ip ∘ trPrNat ip ∘ nat ^$ R.randomIO @ℕ64
      ℤT ip → io $ IntV ip ∘ trPrInt ip ∘ int ^$ R.randomIO @ℤ64
      𝔽T fp → io $ FltV fp ^$ R.randomIO @𝔻
      𝔹T → io $ BoolV ^$ R.randomIO @𝔹
      _ → error "TODO: not implemented"
    wrap v
  RandRangeE τ e → do
    si₀ :* τ' ← case τ of
      ShareT φ ρes τ' → do
        ρvs ← prinExpValss *$ mapM interpPrinExp ρes
        return $ Shared False φ ρvs :* τ'
      _ → return $ NotShared :* τ
    ṽ ← interpExp e
    ṽ₁ :* ṽ₂ ← 
      elim𝑂 
        (throwIErrorCxt TypeIError "interpExp: ReadRangeE: Expected a pair argument" $ 
           frhs [ ("ṽ",pretty ṽ) ]) 
           return $ view pairVPL ṽ
    si₁ :* v₁ ← unShareValP ṽ₁
    si₂ :* v₂ ← unShareValP ṽ₂
    md₁ :* bv₁ ← error𝑂 (frhs ^$ view baseMVL v₁) $ throwIErrorCxt TypeIError "not base val" null
    md₂ :* bv₂ ← error𝑂 (frhs ^$ view baseMVL v₂) $ throwIErrorCxt TypeIError "not base val" null
    bv' ← case (τ',bv₁,bv₂) of
      (ℕT ip,NatMV ip₁ n₁,NatMV ip₂ n₂)                             | (ip₁ ≡ ip) ⩓ (ip₂ ≡ ip) → do io $ NatMV ip ∘ nat ^$ (R.randomRIO @ℕ64) (HS.fromIntegral n₁,HS.fromIntegral n₂)
      (ℤT ip,IntMV ip₁ i₁,IntMV ip₂ i₂) | (ip₁ ≡ ip) ⩓ (ip₂ ≡ ip) → io $ IntMV ip ∘ int ^$ (R.randomRIO @ℤ64) (HS.fromIntegral i₁,HS.fromIntegral i₂)
      (𝔽T fp,FltMV fp₁ d₁,FltMV fp₂ d₂) | (fp₁ ≡ fp) ⩓ (fp₂ ≡ fp) → io $ FltMV fp ^$ (R.randomRIO @𝔻) (d₁,d₂)
      _ → throwIErrorCxt NotImplementedIError "rand-range" $ frhs
        [ ("τ',bv₁,bv₂",pretty (τ' :* bv₁ :* bv₂)) ]
    si' ← joinShareInfos [si₀,si₁,si₂]
    let md = 1 + (md₁ ⊔ md₂)
    case si' of
      NotShared → skip
      Shared zk φ ρs → do
        tellL iOutResEvsL $ ResEv zk φ ρs pø pø (getTypeBaseMPC bv₁) null null "RANDR" md ↦ 1
    reShareValP (BaseMV (md₁ ⊔ md₂) bv') si'
  -- InferE
  -- HoleE
  PrimE o es → do
    ṽs ← mapM interpExp es
    si :* vmpcs ← unShareValPs ṽs
    mds :* bvmpcs ← split ^$ error𝑂 (mapMOn vmpcs $ view baseMVL) $ throwIErrorCxt TypeIError "bad" null
    let md = joins mds
    md' :* bvmpc ← interpReportPrim o md si $ list bvmpcs
    reShareValP (BaseMV md' bvmpc) si
  TraceE e₁ e₂ → do
    v ← interpExp e₁
    pptrace v $ interpExp e₂
  SetE ρes → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    introValP $ PrinSetV ρvs
  RefE e → do
    ṽ ← interpExp e
    ℓ ← nextL iStateNextLocL
    modifyL iStateStoreL $ \ σ → (ℓ ↦♮ ṽ) ⩌♮ σ 
    locValP ℓ
  RefReadE e → do 
    ṽ ← interpExp e
    v ← elimValP ṽ
    ℓ ← elimLocV v
    σ ← getL iStateStoreL
    case σ ⋕? ℓ of
      Some ṽ' → restrictValP ṽ'
      None → throwIErrorCxt InternalIError "interpExp: RefReadE: ℓ ∉ dom(σ)" $ frhs
        [ ("ℓ",pretty ℓ)
        , ("dom(σ)",pretty $ keys𝑊 σ)
        ]
  RefWriteE e₁ e₂ → do
    ṽ₁ ← interpExp e₁ 
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    ℓ ← elimLocV v₁
    modifyL iStateStoreL $ \ σ → (ℓ ↦♮ ṽ₂) ⩌♮ σ
    return ṽ₂
  ArrayE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    case v₁ of
      NatV _ n → do
        ℓ ← nextL iStateNextLocL
        ṽ ← introValP $ ArrayV $ vec $ list $ repeat n ṽ₂
        modifyL iStateStoreL $ \ σ → (ℓ ↦♮ ṽ) ⩌♮ σ
        locValP ℓ
      _ → throwIErrorCxt TypeIError "interpExp: ArrayE: v₁ ≠ IntV _ i" $ frhs
        [ ("v₁",pretty v₁) 
        ]
  ArrayReadE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    ℓ ← elimLocV v₁
    case v₂ of
      NatV _ n → do
        σ ← getL iStateStoreL
        case σ ⋕? ℓ of
          Some ṽ' → do
            v' ← elimValP ṽ'
            case v' of
              ArrayV ṽs → case ṽs ⋕? natΩ64 n of
                Some ṽ → restrictValP ṽ
                None → throwIErrorCxt TypeIError "interpExp: ArrayReadE: n ∉ dom(ṽs)" $ frhs
                  [ ("n",pretty n)
                  , ("dom(ṽs)",pretty $ (0,size ṽs - 𝕟64 1))
                  ]
              _ → throwIErrorCxt TypeIError "interpExp: ArrayReadE: v' ≠ ArrayV _" $ frhs
                [ ("v'",pretty v') ]
          None → throwIErrorCxt TypeIError "interpExp: ArrayReadE: ℓ ∉ dom(σ)" $ frhs 
            [ ("ℓ",pretty ℓ)
            , ("dom(σ)",pretty $ keys𝑊 σ)
            ]
      _ → throwIErrorCxt TypeIError "interpExp: ArrayReadE: v₂ ≠ NatV _ _" $ frhs
        [ ("v₁",pretty v₁)
        , ("v₂",pretty v₂)
        ]
  ArrayWriteE (extract → ArrayReadE e₁ e₂) e₃ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    ṽ₃ ← interpExp e₃
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    ℓ ← elimLocV v₁
    case v₂ of
      NatV _ n → do
        σ ← getL iStateStoreL
        case σ ⋕? ℓ of
          Some ṽ' → do
            v' ← elimValP ṽ'
            case v' of
              ArrayV ṽs → 
                if idxOK𝕍 ṽs $ natΩ64 n
                   then do
                     ṽ'' ← introValP $ ArrayV $ set𝕍 (natΩ64 n) ṽ₃ ṽs
                     putL iStateStoreL $ (ℓ ↦♮ ṽ'') ⩌♮ σ
                     return ṽ₃
                    else do
                      throwIErrorCxt TypeIError "interpExp: ArrayWriteE: n ∉ dom(ṽs)" $ frhs
                        [ ("n",pretty n)
                        , ("ṽs",pretty ṽs)
                        ]
              _ → throwIErrorCxt TypeIError "interpExp: ArrayWriteE: v' ≠ ArrayV _" $ frhs
                [ ("v'",pretty v') ]
          None → throwIErrorCxt TypeIError "interpExp: ArrayWriteE: ℓ ∉ dom(σ)" $ frhs 
            [ ("ℓ",pretty ℓ)
            , ("dom(σ)",pretty $ keys𝑊 σ)
            ]
      _ → throwIErrorCxt TypeIError "interpExp: ArrayWriteE: v₂ ≠ NatV _ _" $ frhs
        [ ("v₁",pretty v₁)
        , ("v₂",pretty v₂)
        ]
  SizeE e → do
    ṽ ← interpExp e
    v ← elimValP ṽ
    ℓ ← elimLocV v
    σ ← getL iStateStoreL
    case σ ⋕? ℓ of
      Some ṽ' → do
        v' ← elimValP ṽ'
        case v' of
          ArrayV ṽs → introValP $ NatV InfIPr $ nat $ size ṽs
          _ → throwIErrorCxt TypeIError "interpExp: SizeE: v' ≠ ArrayV _" null
      _ → throwIErrorCxt TypeIError "interpExp: SizeE: ℓ ∉ dom(σ)" null
  DefaultE → introValP DefaultV
  ProcE e → do
    κ :* ṽ ← 
      localizeL iStateMPCContL null $ 
      localL iCxtMPCPathConditionL null $ 
      interpExp e
    si₀ :* vmpc₀ ← unShareValP ṽ
    si :* vmpc ← mfoldrOnFrom (reverse κ) (si₀ :* vmpc₀) $ \ (pcᴿ :* si₁ :* vmpcᴿ₀) (si₂ :*  vmpc) →  do
      si₃ ← joinShareInfo si₁ si₂
      mfoldrOnFrom pcᴿ (si₃ :* vmpcᴿ₀) $ \ (mdᵖᶜ :* bᵖᶜ :* siᵖᶜ) (si :* vmpcᴿ) → do
        si' ← joinShareInfo si siᵖᶜ
        vmpc' ← muxMPCVal mdᵖᶜ si' bᵖᶜ vmpcᴿ vmpc
        return $ si' :* vmpc'
    reShareValP vmpc si
  ReturnE e → do
    ṽ ← interpExp e
    si :* vmpc ← unShareValP ṽ
    pc ← askL iCxtMPCPathConditionL
    modifyL iStateMPCContL $ \ κ → (pc :* si :* vmpc) :& κ
    introValP DefaultV
  NizkWitnessE φ ρes e → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    ṽ ← interpExp e
    v ← elimValP ṽ
    sv ← mpcFrValF v $ \ bv → do
        tellL iOutResEvsL $ ResEv True φ ρvs pø pø (getTypeBaseMPC bv) null null "SHARE" 0 ↦ 1
    reShareValPShared True φ ρvs sv 
  NizkCommitE _φ ρes e → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    ṽ ← interpExp e
    ṽ' ← revealValP True ρvs ṽ
    introValP $ NizkVerifyV ρvs ṽ'

  _ → throwIErrorCxt NotImplementedIError "interpExp: not implemented" null

---------------
-- TOP LEVEL --
---------------

interpTL ∷ TL → ITLM ()
interpTL tl = case extract tl of
  DeclTL _ _ _ → skip
  DefnTL b x ψs e →  do
    let e' = 
          if b 
          then buildUnfixedLambda (annotatedTag tl) x ψs e
          else buildLambda (annotatedTag tl) x ψs e
    v ← asTLM $ interpExp e'
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL ps → do
    let kinds = dict $ mapOn (iter ps) $ \case
          SinglePD ρ → ρ ↦ SinglePK
          ArrayPD ρ n → ρ ↦ SetPK n
    modifyL itlStateDeclPrinsL (kinds ⩌)
  ImportTL path → do
    s ← io $ fread path
    let ts = tokens s
    ls ← io $ tokenizeIO lexer path ts
    tls ← io $ parseIO cpTLs path ls
    interpTLs tls
  _ → pptrace (annotatedTag tl) $ error "interpTL: not implemented"

interpTLs ∷ 𝐿 TL → ITLM ()
interpTLs = eachWith interpTL

-- ==== --
-- MAIN --
-- ==== --

-------------
-- Options --
-------------

data Options = Options
  { optVersion ∷ 𝔹
  , optHelp ∷ 𝔹
  , optDoResources ∷ 𝔹
  , optJustPrint ∷ 𝔹
  , optRandomSeed ∷ 𝑂 ℕ
  , optTestsPath ∷ 𝕊
  , optLibPath ∷ 𝕊
  } 
  deriving (Eq,Ord,Show)
makeLenses ''Options

options₀ ∷ IO Options
options₀ = do
  localTestsExists ← pexists "tests"
  testsPath ←
    if localTestsExists 
    then return "tests"
    else datapath "tests"
  libPathExists ← pexists "lib"
  libPath ←
    if libPathExists
    then return "lib"
    else datapath "lib"
  return $ Options
    { optVersion = False
    , optHelp = False
    , optDoResources = False
    , optJustPrint = False
    , optRandomSeed = None
    , optTestsPath = testsPath
    , optLibPath = libPath
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
             (O.NoArg $ update optDoResourcesL True) $ 
               chars "enable resource estimation"
  , O.Option ['p'] [chars "print"]
             (O.NoArg$ update optJustPrintL True) $ 
               chars "just print the program"
  , O.Option ['s'] [chars "seed"]  
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoExample ∷ [O.OptDescr (Options → Options)]
usageInfoExample = 
  [ O.Option ['r'] [chars "resources"] 
             (O.NoArg $ update optDoResourcesL True) $ 
               chars "enable resource estimation"
  , O.Option ['p'] [chars "print"]
             (O.NoArg$ update optJustPrintL True) $ 
               chars "just print the program"
  , O.Option ['s'] [chars "seed"]  
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoTest ∷ [O.OptDescr (Options → Options)]
usageInfoTest = 
  [ O.Option ['r'] [chars "resources"] 
             (O.NoArg $ update optDoResourcesL True) $ 
               chars "enable resource estimation"
  , O.Option ['s'] [chars "seed"]  
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

initializeIO ∷ Options → IO ()
initializeIO os = exec
  [ case optRandomSeed os of
      None → skip
      Some seed → R.setStdGen $ R.mkStdGen $ HS.fromIntegral seed
  ]

initializeEnv ∷ Options → IParams
initializeEnv os = flip compose θ₀
  [ if optDoResources os then update iParamsDoResourcesL True else id
  ]

interpretFile ∷ IParams → ITLState → 𝕊 → 𝕊 → IO (ITLState ∧ IOut)
interpretFile θ ωtl name path = do
  s ← fread path
  let ts = tokens s
  ls ← tokenizeIO lexer name ts
  tls ← parseIO cpTLs name ls
  ωtl' :* o :* () ← din (pdirectory path) $ runITLMIO θ ωtl name $ eachWith interpTL tls
  return $ ωtl' :* o

interpretFileMain ∷ IParams → ITLState → 𝕊 → 𝕊 → IO (ValP ∧ 𝑂 ValP)
interpretFileMain θ ωtl name path = do
  ωtl' :* _ ← interpretFile θ ωtl name path
  let main = itlStateEnv ωtl' ⋕! var "main"
  o :* v ← evalITLMIO θ ωtl' name $ hijack $ asTLM $ interpApp main $ AllVP BulV
  let expectedO = itlStateEnv ωtl' ⋕? var "expected"
  let fn = string $ HS.takeBaseName $ chars path
  if iParamsDoResources θ
    then do
      dtouch "resources"
      BS.writeFile (chars $ "resources/" ⧺ fn ⧺ ".res") $ JSON.encode $ jsonEvents $ iOutResEvs o
    else skip
  return $ v :* expectedO

printFileMain ∷ 𝕊 → IO ()
printFileMain path = do
  s ← fread path
  let ts = tokens s
  ls ← tokenizeIO lexer path ts
  pprint $ concat $ map (concat ∘ iter ∘ parserContextDisplayL ∘ parserTokenContext) ls

parseOptions ∷ IO (Options ∧ [𝕊])
parseOptions = do
  as ← iargs
  let (fs,nos,ems) = O.getOpt O.RequireOrder (usageInfoTop ⧺ usageInfoRun) $ lazyList $ map chars as
  eachOn ems (out ∘ string)
  os ← compose fs ^$ options₀
  when (optVersion os) $ \ () → do
    out $ "psl version " ⧺ psl_VERSION
  when (optVersion os ⩓ optHelp os) $ \ () → do
    out ""
  when (optHelp os) $ \ () → do
    out "Usage: psl [<command>] [<arguments>] [<target>]"
    out ""
    out $ string $ O.usageInfo (chars "psl [arguments]") usageInfoTop
    out $ string $ O.usageInfo (chars "psl run [arguments] <file>") usageInfoRun
    out $ string $ O.usageInfo (chars "psl example [arguments] <name>")  usageInfoExample
    out $ string $ O.usageInfo (chars "psl test [arguments]") usageInfoTest
  return $ frhs (os,map string nos)

pslMainRun ∷ IO ()
pslMainRun = do
  (os,ts) ← tohs ^$ parseOptions
  fn ← case ts of
    [] → failIO "ERROR: No file specified as target. Correct usage: psl run [<arguments>] <file>"
    [t] → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: psl run [<arguments>] <file>"
  if optJustPrint os
    then do
      printFileMain fn
      pprint $ ppHorizontal
        [ ppHeader "PRINTING FILE:"
        , ppString fn
        ]
    else do
      pprint $ ppHorizontal
        [ ppHeader "INTERPRETING FILE:"
        , ppString fn
        ]
      initializeIO os
      let θ = initializeEnv os
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" $ optLibPath os ⧺ "/stdlib.psl"
      v ← fst ^$ interpretFileMain θ ωtl fn fn
      pprint $ ppHeader "RESULT"
      pprint v

pslMainExample ∷ IO ()
pslMainExample = do
  (os,ts) ← tohs ^$ parseOptions
  name ← case ts of
    [] → failIO "ERROR: No file specified as target. Correct usage: psl example [<arguments>] <name>"
    [t] → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: psl example [<arguments>] <name>"
  let exampleRelativePath = "examples/" ⧺ name ⧺ ".psl"
  exampleDataFilePath ← datapath exampleRelativePath
  exampleLocalExists ← pexists exampleRelativePath
  exampleDataFileExists ← pexists exampleDataFilePath
  when (not exampleLocalExists ⩓ exampleDataFileExists) $ \ _ → do
    dtouch "examples"
    fcopy exampleDataFilePath exampleRelativePath
  if optJustPrint os
    then do
      pprint $ ppHorizontal 
        [ ppHeader "PRINTING EXAMPLE:"
        , ppString name
        ]
      printFileMain exampleRelativePath
    else do
      pprint $ ppHorizontal 
        [ ppHeader "INTERPRETING EXAMPLE:"
        , ppString name
        ]
      initializeIO os
      let θ = update iParamsIsExampleL True $ initializeEnv os
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" $ optLibPath os ⧺ "/stdlib.psl"
      v ← fst ^$ interpretFileMain θ ωtl (concat ["example:",name,".psl"]) exampleRelativePath
      pprint $ ppHeader "RESULT"
      pprint v

pslMainTest ∷ IO ()
pslMainTest = do
  (os,ts) ← tohs ^$ parseOptions
  case ts of
    [] → skip
    _ → failIO "ERROR: Command does not accept targets. Correct usage: psl test [<arguments>]"
  let θ = initializeEnv os
  pprint $ ppHeader "TESTING INTERPRETER"
  ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" $ optLibPath os ⧺ "/stdlib.psl"
  din (optTestsPath os) $ do
    fns ← dfiles
    vevs ← mapMOn fns $ \ fn → do
      initializeIO os
      (fn :*) ^$ interpretFileMain θ ωtl (concat ["test:",fn]) fn
    pprint $ ppVertical
      [ ppHeader "TESTS"
      , concat
        [ ppSpace $ 𝕟64 2
        , ppAlign $ ppVertical $ mapOn vevs $ \ (fn :* (v :* evO)) → case evO of
            None → ppHorizontal
              [ ppFormat (formats [FG darkYellow]) $ ppString "SKIPPD"
              , ppString fn
              ]
            Some ev →
              if v ≡ ev
              then ppHorizontal 
                [ ppFormat (formats [FG darkGreen]) $ ppString "PASSED"
                , ppString fn
                ]
              else ppVertical
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

pslMainInfo ∷ IO ()
pslMainInfo = do
  out $ concat $ inbetween "\n" 
    [ ""
    , "psl is the interpreter for the PSL language developed by"
    , "the PANTHEON team, funded by IARPA for the HECTOR project."
    , ""
    ]
  (_,ts) ← tohs ^$ parseOptions
  case ts of
    [] → skip
    _ → failIO "ERROR: Command does not accept targets. Correct usage: psl [<arguments>]"

interpreterMain ∷ IO ()
interpreterMain = do
  map list iargs ≫= \case
    "run" :& as → ilocalArgs as $ pslMainRun
    "example" :& as → ilocalArgs as $ pslMainExample
    "test" :& as → ilocalArgs as pslMainTest
    Nil → ilocalArgs (list ["--version","--help"]) pslMainInfo
    as → ilocalArgs as pslMainInfo
