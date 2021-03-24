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
  guardErr (m' ≢ SecM pø) (throwIErrorCxt TypeIError "gm ⊓ m ≡ ∅" $ frhs
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
    f₂ ← bindPatO ψ₁ $ SSecVP (SecM (single ρ)) v
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

bindPatMPC ∷ (STACK) ⇒ Pat → UnShare → FailT IM (IM UnShare → IM UnShare)
bindPatMPC ψ us = case ψ of
  VarP x → return $ \ xM → do
    ṽ ← reShareValP us
    bindVar x ṽ xM
  TupP ψ₁ ψ₂ → do
    us₁ :* us₂ ← viewPairUnShare us
    f₁ ← bindPatMPC ψ₁ us₁
    f₂ ← bindPatMPC ψ₂ us₂
    return $ compose [f₁, f₂]
{-  LP ψ' → do
    c₁ :* cv₂ :* _cv₃ ← view sumCVL cv
    f ← bindPatMPC si ψ' cv₂
    return $ \ xM → do
      si' :* cv' ← mapEnvL iCxtMPCPathConditionL ((c₁ :* si) :&) $ f xM
      cv'' ← muxCktVal c₁ cv' DefaultCV
      si'' ← joinShareInfo si si'
      return $ si'' :* cv''
  RP ψ' → do
    c₁ :* _cv₂ :* cv₃ ← view sumCVL cv
    f ← bindPatMPC si ψ' cv₃
    return $ \ xM → do
      nc₁ ← notCkt c₁
      si' :* cv' ← mapEnvL iCxtMPCPathConditionL ((nc₁ :* si) :&) $ f xM
      cv'' ← muxCktVal c₁ DefaultCV cv'
      si'' ← joinShareInfo si si'
      return $ si'' :* cv''
  NilP → do
    view nilCVL cv
    return id
  ConsP ψ₁ ψ₂ → do
    cv₁ :* cv₂ ← view consCVL cv
    f₁ ← bindPatMPC si ψ₁ cv₁
    f₂ ← bindPatMPC si ψ₂ cv₂
    return $ \ xM → do
      si' :* cv' ← compose [f₁,f₂] xM
      si'' ← joinShareInfo si si'
      return $ si'' :* cv'
  WildP → return id
  _ → error "TODO: not implemented" -}

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

modeCheckShare ∷ 𝑃 PrinVal → 𝑃 PrinVal → IM ()
modeCheckShare ρvsSharer ρvsSharees = do                           -- Formalism:
  gm ← askL iCxtGlobalModeL                                        --   ρvsSharer = p, ρvsSharees = q, gm = m
  let singleSharer    = count ρvsSharer ≡ 1                        --   |p| = 1
  let shareesNonEmpty = ρvsSharees ≢ pø                            --   q ≠ ∅
  let sharerAndShareesPresent = SecM (ρvsSharer ∪ ρvsSharees) ≡ gm --   p ∪ q = m
  guardErr singleSharer $                                          --   p ⊆ p' is handled by shareValP (by way of withValP)
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
    us₁ ← unShareValP ṽ₁
    nus₁ ← notUnShare us₁
    ṽ₂ ← mapEnvL iCxtMPCPathConditionL (us₁ :&) $ interpExp e₂
    ṽ₃ ← mapEnvL iCxtMPCPathConditionL (nus₁ :&) $ interpExp e₃
    us₂ ← unShareValP ṽ₂
    us₃ ← unShareValP ṽ₃
    us' ← muxUnShare us₁ us₂ us₃
    reShareValP us'
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
    us ← unShareValP ṽ
    uss ← concat ^$ mapMOn ψes $ \ (ψ :* e') → do
      bp ← unFailT $ bindPatMPC ψ us
      case bp of
        None → return $ list []
        Some f → single ^$ f $ do
          ṽ' ← interpExp e'
          unShareValP ṽ'
    us' ← mfoldOnFrom uss (NotShared DefaultV) sumUnShare
    reShareValP us'
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
  ShareE φ ρes₁ ρes₂ e → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    modeCheckShare ρvs₁ ρvs₂
    ρv₁ ← fromSome (view one𝑃L ρvs₁)
    ṽ ← interpExp e
    v̂ ← restrictMode (SecM ρvs₁) $ withProt φ $ \ p sp → shareValP p sp ρv₁ ṽ
    return $ ShareVP φ ρvs₂ v̂
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
  RevealE φ ρes₁ ρes₂ e → do -- add a 'from' annotation?
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    modeCheckReveal ρvs₁ ρvs₂
    ṽ ← interpExp e
    v ← restrictMode (SecM ρvs₁) $ withProt φ $ \ p sp → revealValP p sp ρvs₁ ρvs₂ ṽ
    return $ SSecVP (SecM ρvs₂) v
  SendE ρes₁ ρes₂ e → do
    ρvs₁ ← prinExpValss *$ mapM interpPrinExp ρes₁
    ρvs₂ ← prinExpValss *$ mapM interpPrinExp ρes₂
    guardErr (count ρvs₁ ≡ 1) $
      throwIErrorCxt TypeIError "interpExp: SendE: size ρvs₁ ≠ 1" $ frhs
        [ ("ρvs₁",pretty ρvs₁) ]
    gm ← askL iCxtGlobalModeL
    case gm of
      SecM ρs → guardErr (ρvs₂ ⊆ ρs) $
        throwIErrorCxt TypeIError "interpExp: SendE: ρvs ⊈ ρs" $ frhs
          [ ("ρvs₂",pretty ρvs₂)
          , ("ρs",pretty ρs)
          ]
      TopM → skip
    ṽ ← interpExp e
    case ṽ of
      SSecVP m v | (SecM ρvs₁) ⊑ m → return $ SSecVP (SecM ρvs₂) v
      _ → throwIErrorCxt TypeIError "interpExp: SendE: ṽ ∉ {SSecVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]
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
    uss ← mapM unShareValP ṽs
    us' ← primUnShare op uss
    reShareValP us'
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
      BaseV (NatBV _ n) → do
        ℓ ← nextL iStateNextLocL
        ṽ ← introValP $ ArrayV $ vec $ list $ repeat n ṽ₂
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
      BaseV (NatBV _ n) → do
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
          ArrayV ṽs → introValP $ BaseV $ NatBV InfIPr $ nat $ size ṽs
          _ → throwIErrorCxt TypeIError "interpExp: SizeE: v' ≠ ArrayV _" null
      _ → throwIErrorCxt TypeIError "interpExp: SizeE: ℓ ∉ dom(σ)" null
  DefaultE → introValP DefaultV
  ProcE e → do
    κ :* ṽ ←
      localizeL iStateMPCContL null $
      localL iCxtMPCPathConditionL null $
      interpExp e
    us₀ ← unShareValP ṽ
    us ← mfoldrOnFrom (reverse κ) us₀ $ \ (pcᴿ :* us₁) us₂ → mfoldrOnFrom pcᴿ us₁ $ \ usᵖᶜ acc → muxUnShare usᵖᶜ acc us₂
    reShareValP us
  ReturnE e → do
    ṽ ← interpExp e
    us ← unShareValP ṽ
    pc ← askL iCxtMPCPathConditionL
    modifyL iStateMPCContL $ \ κ → (pc :* us) :& κ
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
          then buildUnfixedLambda (annotatedTag tl) x ψs e
          else buildLambda (annotatedTag tl) x ψs e
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

usageInfoExample ∷ [O.OptDescr (Options → Options)]
usageInfoExample =
  [ O.Option ['p'] [chars "print"]
             (O.NoArg$ update optJustPrintL True) $
               chars "just print the program"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoTest ∷ [O.OptDescr (Options → Options)]
usageInfoTest =
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
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" (optLibPath os ⧺ "/stdlib.psl")
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
      ωtl :* _ ← interpretFile θ ωtl₀ "lib:stdlib.psl" (optLibPath os ⧺ "/stdlib.psl")
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
