module PSL.Interpreter where

import UVMHS
import AddToUVMHS

import PSL.Config
import PSL.Parser
import PSL.Syntax

import PSL.Interpreter.Json ()
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.PrinExp
import PSL.Interpreter.ReadType
import PSL.Interpreter.Truncating
import PSL.Interpreter.Types
import PSL.Interpreter.Val
import PSL.Interpreter.Share
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import qualified Prelude as HS
import qualified System.Console.GetOpt as O
import qualified System.Random as R

-------------
-- VERSION --
-------------

restrictMode ∷ (STACK) ⇒ Mode → IM a → IM a
restrictMode m xM = do
  gm ← askL iCxtGlobalModeL
  let m' = gm ⊓ m
  guardErr (m' ≢ SecM pø) (throwIErrorCxt TypeIError "restrictMode: gm ⊓ m ≡ ∅" $ frhs
    [ ("gm",pretty gm)
    , ("m",pretty m)
    ])
  localL iCxtGlobalModeL m' xM

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

--------------
-- PATTERNS --
--------------

bindPat ∷ (STACK) ⇒ Pat → ValP → IM ValP → IM ValP
bindPat ψ ṽ xM = do
  fO ← unFailT $ bindPatValP ψ ṽ
  case fO of
    Some f → f xM
    None → throwIErrorCxt TypeIError "bindPat: no matching cases" $ frhs
      [ ("ψ",pretty ψ)
      , ("ṽ",pretty ṽ)
      ]

interpCase ∷ (STACK) ⇒ ValP → 𝐿 (Pat ∧ Exp) → IM ValP
interpCase ṽ ψes = do
  fO ← unFailT $ interpCaseO ṽ ψes
  case fO of
    None → throwIErrorCxt TypeIError "interpCase: interpCaseO ṽ ψes = None" $ frhs
      [ ("ṽ",pretty ṽ)
      , ("ψes",pretty ψes)
      ]
    Some ṽ' → return ṽ'

interpCaseO ∷ (STACK) ⇒ ValP → 𝐿 (Pat ∧ Exp) → FailT IM ValP
interpCaseO ṽ ψes = case ψes of
  Nil → abort
  (ψ :* e) :& ψes' → tries
    [ do f ← bindPatValP ψ ṽ
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
            Some self → bindVarTo self ṽ₁
      compose [localL iCxtEnvL γ,bindPat ψ ṽ₂,selfγ] $ interpExp e
    _ → throwIErrorCxt TypeIError "interpExp: AppE: v₁ ≢ CloV _ _ _ _" $ frhs
      [ ("v₁",pretty v₁)
      ]

-----------------
-- EXPRESSIONS --
-----------------

-- If all parties who know the value are locally present, don't bother with MPC
sequentialSwitch ∷ Prot → IM Prot
sequentialSwitch φ = do
  gm ← askL iCxtGlobalModeL
  lm ← askL iCxtLocalModeL
  return $ if gm ⊑ lm then PlainP else φ

wrapInterp ∷ (STACK) ⇒ (ExpR → IM ValP) → Exp → IM ValP
wrapInterp f e = localL iCxtSourceL (Some $ atag e) $ f $ extract e

modeCheckShare ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM ()
modeCheckShare ρvsSharer ρvsSharees = do                           -- Formalism:
  gm ← askL iCxtGlobalModeL                                        --   ρvsSharer = p, ρvsSharees = q, gm = m
  let singleSharer    = count ρvsSharer ≡ 1                        --   |p| = 1
  let shareesNonEmpty = ρvsSharees ≢ pø                            --   q ≠ ∅
  let sharerAndShareesPresent = SecM (ρvsSharer ∪ ρvsSharees) ≡ gm --   p ∪ q = m
  guardErr singleSharer $
    throwIErrorCxt TypeIError "modeCheckShare: count ρvsSharer ≢ 1" $ frhs
    [ ("ρvsSharer",pretty ρvsSharer)
    ]
  guardErr shareesNonEmpty $
    throwIErrorCxt TypeIError "modeCheckShare: ρvsSharees ≡ pø" $ frhs
    [ ("ρvsSharees",pretty ρvsSharees)
    ]
  guardErr sharerAndShareesPresent $
    throwIErrorCxt TypeIError "modeCheckShare: SecM (ρvsSharer ∪ ρvsSharees) ≢ gm" $ frhs
    [ ("ρvsSharer", pretty ρvsSharer)
    , ("ρvsSharees", pretty ρvsSharees)
    , ("gm", pretty gm)
    ]

modeCheckReveal ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM ()
modeCheckReveal ρvsRevealers ρvsRevealees = do                               -- Formalism:
  gm ← askL iCxtGlobalModeL                                                  --   ρvsRevealers = p, ρvsRevealees = q, gm = m
  let revealeesNonEmpty = ρvsRevealees ≢ pø                                  --   q ≠ ∅
  let revealersAndRevealeesPresent = SecM (ρvsRevealers ∪ ρvsRevealees) ≡ gm --   p ∪ q = m
  guardErr revealeesNonEmpty $
    throwIErrorCxt TypeIError "modeCheckReveal: ρvsRevealees ≡ pø" $ frhs
    [ ("ρvsRevealees",pretty ρvsRevealees)
    ]
  guardErr revealersAndRevealeesPresent $
    throwIErrorCxt TypeIError "modeCheckReveal: SecM (ρvsRevealers ∪ ρvsRevealees) ≢ gm" $ frhs
    [ ("ρvsRevealers",pretty ρvsRevealers)
    , ("ρvsRevealees",pretty ρvsRevealees)
    , ("gm", pretty gm)
    ]

modeCheckSend ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM ()
modeCheckSend ρvsFr ρvsTo = do
  gm ← askL iCxtGlobalModeL
  let singleFr = count ρvsFr ≡ 1
  let presentTo = (SecM ρvsTo) ⊑ gm
  guardErr singleFr $
    throwIErrorCxt TypeIError "modeCheckSend: count ρvsFr ≢ 1" $ frhs [ ("ρvsFr", pretty ρvsFr) ]
  guardErr presentTo $
    throwIErrorCxt TypeIError "modeCheckSend: (SecM ρvsTo) ⋢ gm" $ frhs [ ("ρvsTo", pretty ρvsTo), ("gm", pretty gm) ]

interpExp ∷ (STACK) ⇒ Exp → IM ValP
interpExp = wrapInterp $ \case
  VarE x → restrictValP *$ interpVar x
  BoolE b → introValP $ BaseV $ BoolBV b
  StrE s → introValP $ StrV s
  NatE pr n → introValP $ BaseV $ NatBV pr $ trPrNat pr n
  IntE pr i → introValP $ BaseV $ IntBV pr $ trPrInt pr i
  FltE pr f → introValP $ BaseV $ FltBV pr $ f --trPrFlt pr f (trPrFlt needs to be written)
  BulE → introValP BulV
  IfE e₁ e₂ e₃ → do
    ṽ ← interpExp e₁
    v ← elimValP ṽ
    b ← error𝑂 (view (boolBVL ⊚ baseVL) v) (throwIErrorCxt TypeIError "interpExp: IfE: view boolVL v ≡ None" $ frhs
                                            [ ("v",pretty v)
                                            ])
    if b
      then interpExp e₂
      else interpExp e₃
  MuxIfE e₁ e₂ e₃ → do
    ṽ₁ ← interpExp e₁
    negṽ₁ ← notValP ṽ₁
    ṽ₂ ← mapEnvL iCxtMPCPathConditionL (ṽ₁ :&) $ interpExp e₂
    ṽ₃ ← mapEnvL iCxtMPCPathConditionL (negṽ₁ :&) $ interpExp e₃
    ṽ ← muxValP ṽ₁ ṽ₂ ṽ₃
    return ṽ
  LE e → do
    ṽ ← interpExp e
    introValP $ LV ṽ
  RE e → do
    ṽ ← interpExp e
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
  LetTyE _ e → interpExp e
  LetE ψ e₁ e₂ → do
    ṽ ← interpExp e₁
    bindPat ψ ṽ $ interpExp e₂
  CaseE e ψes → do
    ṽ ← interpExp e
    interpCase ṽ ψes
  MuxCaseE e ψes → do
    ṽ ← interpExp e
    ṽs ← concat ^$ mapMOn ψes $ \ (ψ :* e') → do
      bp ← unFailT $ bindPatValP ψ ṽ
      case bp of
        None → return $ list []
        Some f → single ^$ f $ interpExp e'
    ṽd ← introValP DefaultV
    mfold ṽd sumValP ṽs
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
  ParE ρes oτ e → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    restrictMode (SecM ρvs) $ do
      gm ← askL iCxtGlobalModeL
      lm ← askL iCxtLocalModeL
      if gm ⊓ lm ≡ SecM pø
        then do
        τ ← error𝑂 oτ (throwIErrorCxt NotImplementedIError "interpExp: ParE: mτ ≡ None" $ frhs
                       [ ("oτ",pretty oτ)
                       ])
        introValP $ UnknownV τ
      else interpExp e
  ShareE prot ρes₁ ρes₂ e → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    modeCheckShare ρvs₁ ρvs₂
    ρv₁ ← fromSome $ view one𝑃L ρvs₁
    prot' ← sequentialSwitch prot
    restrictMode (SecM ρvs₁) $ do
      ṽ ← interpExp e
      withProt prot' $ \ p φ → shareValP p φ ρvs₂ ρv₁ ṽ
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
    return $ SSecVP (SecM (single ρv)) v
  BundleE ρes → do
    ISecVP ^$ dict ^$ mapMOn (iter ρes) $ \ (ρ :* e) → do
      ρv ← interpPrinExpSingle ρ
      ṽ ← restrictMode (SecM $ single ρv) $ interpExp e
      m :* v ← error𝑂 (view sSecVPL ṽ) (throwIErrorCxt TypeIError "interpExp: BundleE: view sSecVPL ṽ ≡ None" $ frhs
                                         [ ("ṽ",pretty ṽ)
                                         ])
      guardErr (m ≡ SecM (single ρv)) (throwIErrorCxt TypeIError "interpExp: BundleE: m ≢ SecM (single ρv)" $ frhs
                                  [ ("m",pretty m)
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
  RevealE prot ρes₁ ρes₂ e → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    modeCheckReveal ρvs₁ ρvs₂
    prot' ← sequentialSwitch prot
    restrictMode (SecM ρvs₁) $ do
      ṽ ← interpExp e
      withProt prot' $ \ p φ → revealValP p φ ρvs₁ ρvs₂ ṽ
  SendE ρes₁ ρes₂ e → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    modeCheckSend ρvs₁ ρvs₂
    ρv₁ ← fromSome $ view one𝑃L ρvs₁
    restrictMode (SecM ρvs₁) $ do
      ṽ ← interpExp e
      sendValP ρvs₂ ρv₁ ṽ
  -- AscrE
  ToStringE e → do
    ṽ ← interpExp e
    v ← elimValP ṽ
    case v of
      BaseV (NatBV _p n) → introValP $ StrV $ show𝕊 n
      BaseV (IntBV _p i) → introValP $ StrV $ show𝕊 i
      BaseV (FltBV _p f) → introValP $ StrV $ show𝕊 f
      _ → throwIErrorCxt TypeIError "interpExp: ToStringE: v ∉ {NatV _ _ , IntV _ _, FltV _ _}" $ null
  StringConcatE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    case (v₁,v₂) of
      (StrV s₁, StrV s₂) → introValP $ StrV (s₁ ⧺ s₂)
      _ → throwIErrorCxt TypeIError "interpExp: StringConcatE: v₁,v₂ ∉ {StrV _}" $ null
  ReadE τA e → do
    ṽ ← interpExp e
    v ← elimValP ṽ
    m ← askL iCxtGlobalModeL
    case (v,m) of
      (StrV fn,SecM ρs) | [ρ] ← tohs $ list ρs → do
        v' ← readType ρ τA fn
        return $ SSecVP (SecM (single ρ)) v'
      _ → throwIErrorCxt TypeIError "interpExp: ReadE: (v,m) ≠ (StrV _,SecM {_})" $ frhs
        [ ("v",pretty v)
        , ("m",pretty m)
        ]
  WriteE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    m ← askL iCxtGlobalModeL
    case (m,v₂) of
      (SecM ρs,StrV fn) | [ρ] ← tohs $ list ρs → do
        writeVal ρ v₁ fn
        introValP BulV
      _ → throwIErrorCxt TypeIError "interpExp: WriteE: m ≠ SecM {ρ}" null
  PrimE op es → do
    ṽs ← mapM interpExp es
    primValP op ṽs
  TraceE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    pptraceM ṽ₁
    interpExp e₂
  SetE ρes → do
    ρvs ← prinExpValss *$ mapM interpPrinExp ρes
    introValP $ PrinSetV ρvs
  RefE e → do
    ṽ ← interpExp e
    ℓ ← nextL iStateNextLocL
    modifyL iStateStoreL $ \ σ → (ℓ ↦♮ ṽ) ⩌♮ σ
    introLocV ℓ ≫= introValP
  RefReadE e → do
    ṽ ← interpExp e
    v ← elimValP ṽ
    ℓ ← elimLocV v
    σ ← getL iStateStoreL
    case σ ⋕? ℓ of
      Some ṽ' → restrictValP ṽ'
      None → throwIErrorCxt InternalIError "interpExp: RefReadE: ℓ ∉ dom(σ)" $ frhs
        [ ("ℓ",pretty ℓ)
        , ("dom(σ)",pretty $ keys𝑉 σ)
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
      BaseV (NatBV _ n) → do
        ℓ ← nextL iStateNextLocL
        ṽ ← introValP $ ArrayV $ repeat𝑉 (intΩ64 n) ṽ₂
        modifyL iStateStoreL $ \ σ → (ℓ ↦♮ ṽ) ⩌♮ σ
        introLocV ℓ ≫= introValP
      _ → throwIErrorCxt TypeIError "interpExp: ArrayE: v₁ ≠ NatV _ n" $ frhs
        [ ("v₁",pretty v₁)
        ]
  ArrayReadE e₁ e₂ → do
    ṽ₁ ← interpExp e₁
    ṽ₂ ← interpExp e₂
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    ℓ ← elimLocV v₁
    case v₂ of
      BaseV (NatBV _ n) → do
        σ ← getL iStateStoreL
        case σ ⋕? ℓ of
          Some ṽ' → do
            v' ← elimValP ṽ'
            case v' of
              ArrayV ṽs → case ṽs ⋕? intΩ64 n of
                Some ṽ → restrictValP ṽ
                None → throwIErrorCxt TypeIError "interpExp: ArrayReadE: n ∉ dom(ṽs)" $ frhs
                  [ ("n",pretty n)
                  , ("dom(ṽs)",pretty $ (0,count ṽs - 𝕟64 1))
                  ]
              _ → throwIErrorCxt TypeIError "interpExp: ArrayReadE: v' ≠ ArrayV _" $ frhs
                [ ("v'",pretty v') ]
          None → throwIErrorCxt TypeIError "interpExp: ArrayReadE: ℓ ∉ dom(σ)" $ frhs
            [ ("ℓ",pretty ℓ)
            , ("dom(σ)",pretty $ keys𝑉 σ)
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
      BaseV (NatBV _ n) → do
        σ ← getL iStateStoreL
        case σ ⋕? ℓ of
          Some ṽ' → do
            v' ← elimValP ṽ'
            case v' of
              ArrayV ṽs →
                if isSome $ ṽs ⋕? intΩ64 n
                   then do
                     ṽ'' ← introValP $ ArrayV $ ((intΩ64 n) ↦♮ ṽ₃) ⩌♮ ṽs
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
            , ("dom(σ)",pretty $ keys𝑉 σ)
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
          ArrayV ṽs → introValP $ BaseV $ NatBV InfIPr $ count ṽs
          _ → throwIErrorCxt TypeIError "interpExp: SizeE: v' ≠ ArrayV _" null
      _ → throwIErrorCxt TypeIError "interpExp: SizeE: ℓ ∉ dom(σ)" null
  DefaultE → introValP DefaultV
  ProcE e → do
    κ :* ṽ₀ ←
      localizeL iStateMPCContL null $
      localL iCxtMPCPathConditionL null $
      interpExp e
    mfoldrOnFrom (reverse κ) ṽ₀ $ \ (pcᴿ :* ṽ₁) ṽ₂ → mfoldrOnFrom pcᴿ ṽ₁ $ \ ṽᵖᶜ acc → muxValP ṽᵖᶜ acc ṽ₂
  ReturnE e → do
    ṽ ← interpExp e
    pc ← askL iCxtMPCPathConditionL
    modifyL iStateMPCContL $ \ κ → (pc :* ṽ) :& κ
    introValP DefaultV
  _ → throwIErrorCxt NotImplementedIError "interpExp: not implemented" null

---------------
-- TOP LEVEL --
---------------

asTLM ∷ IM a → ITLM a
asTLM xM = do
  vps ← askL iParamsVirtualPartyArgsL
  mkITLM $ \ θ ωtl → do
    let ds = itlStateDeclPrins ωtl
        -- princpal declarations as values
        γ' = dict $ mapOn (iter $ itlStateDeclPrins ωtl) $ \ (ρ :* κ) → case κ of
          SinglePK → (var ρ ↦) $ SSecVP TopM $ PrinV $ ValPEV $ SinglePV ρ
          SetPK n → (var ρ ↦) $ SSecVP TopM $ PrinV $ SetPEV n ρ
          VirtualPK → (var ρ ↦) $ SSecVP TopM $ PrinV $ case vps ⋕? ρ of
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

interpTL ∷ TL → ITLM ()
interpTL tl = case extract tl of
  DeclTL _ _ _ → skip
  DefnTL b x ψs e →  do
    let e' =
          if b
          then buildUnfixedLambda (atag tl) x ψs e
          else buildLambda (atag tl) x ψs e
    v ← asTLM $ interpExp e'
    modifyL itlStateEnvL ((x ↦ v) ⩌)
  PrinTL ps → do
    let kinds = dict $ mapOn (iter ps) $ \case
          SinglePD ρ → ρ ↦ SinglePK
          ArrayPD ρ n → ρ ↦ SetPK n
    modifyL itlStateDeclPrinsL (kinds ⩌)
  ImportTL path xρss → do
    xρvs ← assoc ^$ mapMOn xρss $ \ (x :* ρs) → do
      ρv ← asTLM $ prinExpValss *$ mapM interpPrinExp ρs
      return $ x :* ρv
    s ← io $ fread path
    let ts = tokens s
    ls ← io $ tokenizeIO lexer path ts
    tls ← io $ parseIO cpTLs path ls
    mapEnvL iParamsVirtualPartyArgsL ((⩌) xρvs) $
      interpTLs tls
  VirtualPartyTL ρs → do
    modifyL itlStateDeclPrinsL $ (⩌) $
      dict $ mapOn ρs $ \ ρ → ρ ↦ VirtualPK
  _ → let _ = pptrace (atag tl) in error "interpTL: not implemented"

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
  , optJustPrint ∷ 𝔹
  , optRandomSeed ∷ 𝑂 ℕ
  , optParty ∷ 𝑂 Prin
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
    , optJustPrint = False
    , optRandomSeed = None
    , optParty = None
    , optTestsPath = testsPath
    , optLibPath = libPath
    }

usageInfoTop ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTop = frhs
  [ O.Option ['v'] [chars "version"]
             (O.NoArg $ update optVersionL True)
           $ chars "print version"
  , O.Option ['h'] [chars "help"]
             (O.NoArg $ update optHelpL True)
           $ chars "show help"
  ]

usageInfoRun ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoRun = frhs
  [ O.Option ['p'] [chars "print"]
             (O.NoArg$ update optJustPrintL True) $
               chars "just print the program"
  , O.Option ['P'] [chars "party"]
             (O.ReqArg (\ s → update optPartyL $ Some $ string s) $ chars "PRIN")
           $ chars "set current party"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoExample ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoExample = frhs
  [ O.Option ['p'] [chars "print"]
             (O.NoArg$ update optJustPrintL True) $
               chars "just print the program"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoTest ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTest = frhs
  [ O.Option ['s'] [chars "seed"]
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
  [ case optParty os of
      None           → id
      Some localMode → update iParamsLocalModeL $ SecM $ single $ SinglePV localMode
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
  v ← evalITLMIO θ ωtl' name $ asTLM $ interpApp main $ SSecVP TopM BulV
  let expectedO = itlStateEnv ωtl' ⋕? var "expected"
  return $ v :* expectedO

printFileMain ∷ 𝕊 → IO ()
printFileMain path = do
  s ← fread path
  let ts = tokens s
  ls ← tokenizeIO lexer path ts
  pprint $ concat $ map (concat ∘ iter ∘ parserContextDisplayL ∘ parserTokenContext) ls

parseOptionsPSL ∷ IO (Options ∧ 𝐿 𝕊)
parseOptionsPSL = do
  as ← iargs
  let fs :* nos :* ems = parseOptions (usageInfoTop ⧺ usageInfoRun) as
  eachOn ems out
  os ← compose fs ^$ options₀
  when (optVersion os) $ do
    out $ "psl version " ⧺ psl_VERSION
  when (optVersion os ⩓ optHelp os) $ do
    out ""
  when (optHelp os) $ do
    out "Usage: psl [<command>] [<arguments>] [<target>]"
    out ""
    out $ optUsageInfo "psl [arguments]" usageInfoTop
    out $ optUsageInfo "psl run [arguments] <file>" usageInfoRun
    out $ optUsageInfo "psl example [arguments] <name>"  usageInfoExample
    out $ optUsageInfo "psl test [arguments]" usageInfoTest
  return $ os :* nos

pslMainRun ∷ IO ()
pslMainRun = do
  os :* ts ← parseOptionsPSL
  fn ← case ts of
    Nil      → failIO "ERROR: No file specified as target. Correct usage: psl run [<arguments>] <file>"
    t :& Nil → return t
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
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" (optLibPath os ⧺ "/stdlib.psl")
      v ← fst ^$ interpretFileMain θ ωtl fn fn
      pprint $ ppHeader "RESULT"
      pprint v

pslMainExample ∷ IO ()
pslMainExample = do
  os :* ts ← parseOptionsPSL
  name ← case ts of
    Nil      → failIO "ERROR: No file specified as target. Correct usage: psl example [<arguments>] <name>"
    t :& Nil → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: psl example [<arguments>] <name>"
  let exampleRelativePath = "examples/" ⧺ name ⧺ ".psl"
  exampleDataFilePath ← datapath exampleRelativePath
  exampleLocalExists ← pexists exampleRelativePath
  exampleDataFileExists ← pexists exampleDataFilePath
  when (not exampleLocalExists ⩓ exampleDataFileExists) $ do
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
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" (optLibPath os ⧺ "/stdlib.psl")
      v ← fst ^$ interpretFileMain θ ωtl (concat ["example:",name,".psl"]) exampleRelativePath
      pprint $ ppHeader "RESULT"
      pprint v

pslMainTest ∷ IO ()
pslMainTest = do
  os :* ts ← parseOptionsPSL
  case ts of
    Nil → skip
    _   → failIO "ERROR: Command does not accept targets. Correct usage: psl test [<arguments>]"
  let θ = initializeEnv os
  pprint $ ppHeader "TESTING INTERPRETER"
  ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" (optLibPath os ⧺ "/stdlib.psl")
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
              [ ppFormat (formats [FG yellow]) $ ppString "SKIPPD"
              , ppString fn
              ]
            Some ev →
              if v ≡ ev
              then ppHorizontal
                [ ppFormat (formats [FG green]) $ ppString "PASSED"
                , ppString fn
                ]
              else ppVertical
                [ ppHorizontal
                    [ ppFormat (formats [FG red]) $ ppString "FAILED"
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
  _ :* ts ← parseOptionsPSL
  case ts of
    Nil → skip
    _   → failIO "ERROR: Command does not accept targets. Correct usage: psl [<arguments>]"

interpreterMain ∷ IO ()
interpreterMain = do
  map list iargs ≫= \case
    "run" :& as → ilocalArgs as $ pslMainRun
    "example" :& as → ilocalArgs as $ pslMainExample
    "test" :& as → ilocalArgs as pslMainTest
    Nil → ilocalArgs (list ["--version","--help"]) pslMainInfo
    as → ilocalArgs as pslMainInfo
