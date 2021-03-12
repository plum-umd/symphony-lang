module PSL.Interpreter.Access where

import UVMHS
import AddToUVMHS

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Json ()
import PSL.Interpreter.Primitives
import PSL.Interpreter.Circuits

-- enter a strictly smaller mode than the current one
restrictMode ∷ (STACK) ⇒ Mode → IM a → IM a
restrictMode m' xM = do
  m ← askL iCxtGlobalModeL
  let m'' = m ⊓ m'
  guardErr (m'' ≢ SecM pø) (throwIErrorCxt TypeIError "m ⊓ m' ≡ ∅" $ frhs
    [ ("m",pretty m)
    , ("m'",pretty m')
    ])
  localL iCxtGlobalModeL m'' xM

-- restrict the mode on a value to be no larger than execution mode
-- e.g.:
-- ‣ if current mode is {par:A,B} and value is {ssec:C} this fails
-- ‣ if current mode is {par:A,B} and value is {ssec:A}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B,C}, this succeeds with value in {ssec:A,B}
restrictValP ∷ (STACK) ⇒ ValP → IM ValP
restrictValP ṽ = do
  m ← askL iCxtGlobalModeL
  case (m,ṽ) of
    (SecM ρs₁, SSecVP ρs₂ v) → do
      v' ← restrictValPRecVal v
      let ρs = ρs₁ ∩ ρs₂
      return $ SSecVP ρs v'
    (SecM ρs, ISecVP ρvs) → do
      let ρvs' = restrict ρs ρvs --TODO(ins): why no recursive call here?
      return $ ISecVP ρvs'
    (SecM ρs₁, ShareVP φ ρs₂ v) → do
      guardErr (ρs₂ ≡ ρs₁) (throwIErrorCxt TypeIError "restrictValP: ρs₂ ≢ ρs₁" $ frhs
                            [ ("ρs₁",pretty ρs₁)
                            , ("ρs₂",pretty ρs₂)
                            ])
      return $ ShareVP φ ρs₂ v
    (SecM ρs, AllVP v) → do
      v' ← restrictValPRecVal v
      return $ SSecVP ρs v'
    (TopM,_) → return ṽ

restrictValPRecVal ∷ (STACK) ⇒ Val → IM Val
restrictValPRecVal v = case v of
  BoolV _ → return v
  StrV _ → return v
  NatV _ _ → return v
  IntV _ _ → return v
  FltV _ _ → return v
  BulV → return v
  LV ṽ → do
    v' ← restrictValP ṽ
    return $ LV v'
  RV ṽ → do
    v' ← restrictValP ṽ
    return $ RV v'
  NilV → return v
  ConsV ṽ₁ ṽ₂ → do
    v₁ ← restrictValP ṽ₁
    v₂ ← restrictValP ṽ₂
    return $ ConsV v₁ v₂
  CloV _ _ _ _  → return v
  TCloV _ _ _ → return v
  PrinV _ → return v
  PrinSetV _ → return v
  LocV _ _ → return v
  ArrayV ṽs → ArrayV ∘ vec ^$ mapMOn (list ṽs) restrictValP
  PairV ṽ₁ ṽ₂ → do
    v₁ ← restrictValP ṽ₁
    v₂ ← restrictValP ṽ₂
    return $ PairV v₁ v₂
  UnknownV _ → return v
  DefaultV → return DefaultV

-- create a value known to current mode
introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  m ← askL iCxtGlobalModeL
  return $ case m of
    SecM ρs → SSecVP ρs v
    TopM → AllVP v

-- look at a value; fails if value has mode smaller than execution mode
-- e.g.,
-- ‣ if current mode is {par:A,B} and value is {ssec:C} this fails
-- ‣ if current mode is {par:A,B} and value is {ssec:A} this fails
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B} this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B,C} this succeeds
elimValP ∷ (STACK) ⇒ ValP → IM Val
elimValP ṽ = do
  m ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP ρs v' → do
      guardErr (m ⊑ SecM ρs) $
        throwIErrorCxt TypeIError "elimValP: m ⋢ PSecM ρs" $ frhs
          [ ("m",pretty m)
          , ("ρs",pretty ρs)
          ]
      return v'
    AllVP v' → return v'
    _ → throwIErrorCxt TypeIError "elimValP: ṽ ∉ {SSecVP _ _, AllVP _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]

-- create a location fixed to the current mode
introLocV ∷ (STACK) ⇒ ℤ64 → IM Val
introLocV ℓ = do
  m ← askL iCxtGlobalModeL
  return $ LocV m ℓ

elimLocV ∷ (STACK) ⇒ Val → IM ℤ64
elimLocV v = do
  m ← askL iCxtGlobalModeL
  case v of
    LocV m' ℓ → do
      guardErr (m ≡ m') $
        throwIErrorCxt TypeIError "elimLocV: m ≠ m'" $ frhs
          [ ("m",pretty m)
          , ("m'",pretty m')
          ]
      return ℓ
    _ → throwIErrorCxt TypeIError "elimLocV: v ≠ LocV _ _" $ frhs
          [ ("v",pretty v) ]

joinShareInfo ∷ (STACK) ⇒ ShareInfo → ShareInfo → IM ShareInfo
joinShareInfo si₁ si₂ = case (si₁,si₂) of
  (NotShared,_) → return si₂
  (_,NotShared) → return si₁
  (Shared φ₁ ρs₁,Shared φ₂ ρs₂)
    | (φ₁ ≡ φ₂) ⩓ (ρs₁ ≡ ρs₂) → return $ Shared φ₁ ρs₁
  _ → throwIErrorCxt TypeIError "bad" null

joinShareInfos ∷ (STACK,ToIter ShareInfo t) ⇒ t → IM ShareInfo
joinShareInfos = mfoldFromWith NotShared joinShareInfo

shareValP ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → ValP → IM CktVal
shareValP φ ρvsFrom ρvsTo = \case
  SSecVP ρs v → do
    guardErr (ρvsFrom ⊆ ρs) $ throwIErrorCxt TypeIError "shareValP: SSecVP: ¬ (SecM ρvsFrom) ⊑ ρs " $ frhs
      [ ("ρvsFrom",pretty ρvsFrom)
      , ("ρs",pretty ρs)
      ]
    shareVal φ ρvsFrom ρvsTo v
  ShareVP _φ _ρs _cv → throwIErrorCxt TypeIError "shareValP: ShareVP: cannot share a share." $ frhs
    [ ("_φ", pretty _φ)
    , ("_ρs", pretty _ρs)
    , ("_cv", pretty _cv)
    ]
  AllVP v → shareVal φ ρvsFrom ρvsTo v
  ṽ → throwIErrorCxt TypeIError "shareValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _,AllVP _}" $ frhs
    [ ("ṽ",pretty ṽ) ]

shareVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → IM CktVal
shareVal φ ρvsFrom ρvsTo = \case
  BoolV b → do
    c ← boolInputCkt ρvsFrom b
    return $ BaseCV c
  NatV pr n → do
    c ← natInputCkt ρvsFrom pr n
    return $ BaseCV c
  IntV pr i → do
    c ← intInputCkt ρvsFrom pr i
    return $ BaseCV c
  FltV pr f → do
    c ← fltInputCkt ρvsFrom pr f
    return $ BaseCV c
  PrinV (ValPEV ρe) → do
    c ← prinInputCkt ρvsFrom (AddBTD ρe)
    return $ BaseCV c
  PairV ṽ₁ ṽ₂ → do
    cv₁ ← shareValP φ ρvsFrom ρvsTo ṽ₁
    cv₂ ← shareValP φ ρvsFrom ρvsTo ṽ₂
    return $ PairCV cv₁ cv₂
  LV ṽ → do
    tt ← trueInputCkt ρvsFrom
    cv ← shareValP φ ρvsFrom ρvsTo ṽ
    return $ SumCV tt cv DefaultCV
  RV ṽ → do
    ff ← falseInputCkt ρvsFrom
    cv ← shareValP φ ρvsFrom ρvsTo ṽ
    return $ SumCV ff DefaultCV cv
  NilV → return $ NilCV
  ConsV ṽ₁ ṽ₂ → do
    cv₁ ← shareValP φ ρvsFrom ρvsTo ṽ₁
    cv₂ ← shareValP φ ρvsFrom ρvsTo ṽ₂
    return $ ConsCV cv₁ cv₂
  BulV → return BulCV
  UnknownV τ → shareValType φ ρvsFrom ρvsTo τ
  v → throwIErrorCxt NotImplementedIError "shareVal" $ frhs
      [ ("φ",pretty φ)
      , ("ρvsFrom",pretty ρvsFrom)
      , ("ρvsTo",pretty ρvsTo)
      , ("v",pretty v)
      ]

shareValType ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Type → IM CktVal
shareValType φ ρvsFrom ρvsTo = \case
    τ | base τ → do
      c ← inputCkt ρvsFrom (UnavailableI τ)
      return $ BaseCV c
    UnitT → return $ BulCV
    τ₁ :×: τ₂ → do
      cv₁ ← shareValType φ ρvsFrom ρvsTo τ₁
      cv₂ ← shareValType φ ρvsFrom ρvsTo τ₂
      return $ PairCV cv₁ cv₂
    τ₁ :+: τ₂ → do
      c ← inputCkt ρvsFrom (UnavailableI 𝔹T)
      cv₁ ← shareValType φ ρvsFrom ρvsTo τ₁
      cv₂ ← shareValType φ ρvsFrom ρvsTo τ₂
      return $ SumCV c cv₁ cv₂
    ListT τ' → throwIErrorCxt NotImplementedIError "shareValType: ListT τ" $ frhs
              [ ("φ",pretty φ)
              , ("ρvsFrom",pretty ρvsFrom)
              , ("ρvsTo",pretty ρvsTo)
              , ("τ'",pretty τ')
              ]
    τ → throwIErrorCxt TypeIError "shareValType: sharing type τ not supported" $ frhs
        [ ("φ",pretty φ)
        , ("ρvsFrom",pretty ρvsFrom)
        , ("ρvsTo",pretty ρvsTo)
        , ("τ",pretty τ)
        ]

  where base 𝔹T = True
        base (ℕT _) = True
        base (ℤT _) = True
        base (𝔽T _) = True
        base ℙT = True
        base _ = False

unShareValP ∷ (STACK) ⇒ ValP → IM (ShareInfo ∧ CktVal)
unShareValP ṽ = do
  m ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP ρs v → do
      guardErr (m ⊑ SecM ρs) $
        throwIErrorCxt TypeIError "unShareValP: SSecVP: ¬ m ⊑ SecM ρs " $ frhs
        [ ("m",pretty m)
        , ("ρs",pretty ρs)
        ]
      unShareVal v
    ShareVP φ ρs cv → do
      guardErr (SecM ρs ≡ m) $
        throwIErrorCxt TypeIError "unShareValP: SecM ρs ≢ m" $ frhs
        [ ("ρs", pretty ρs)
        , ("m", pretty m)
        ]
      return $ (Shared φ ρs) :* cv
    AllVP v → unShareVal v
    _ → throwIErrorCxt TypeIError "unShareValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _,AllVP _}" $ frhs
        [ ("ṽ",pretty ṽ) ]

unShareVal ∷ (STACK) ⇒ Val → IM (ShareInfo ∧ CktVal)
unShareVal = \case
  BoolV b → do
    c ← boolCkt b
    return $ NotShared :* BaseCV c
  NatV pr n → do
    c ← natCkt pr n
    return $ NotShared :* BaseCV c
  IntV pr i → do
    c ← intCkt pr i
    return $ NotShared :* BaseCV c
  FltV pr i → do
    c ← fltCkt pr i
    return $ NotShared :* BaseCV c
  PrinV (ValPEV ρe) → do
    c ← prinCkt (AddBTD ρe)
    return $ NotShared :* BaseCV c
  PairV ṽ₁ ṽ₂ → do
    si₁ :* cv₁ ← unShareValP ṽ₁
    si₂ :* cv₂ ← unShareValP ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* PairCV cv₁ cv₂
  LV ṽ → do
    si :* cv ← unShareValP ṽ
    tt ← trueCkt
    return $ si :* SumCV tt cv DefaultCV
  RV ṽ → do
    si :* cv ← unShareValP ṽ
    ff ← falseCkt
    return $ si :* SumCV ff DefaultCV cv
  NilV → return $ NotShared :* NilCV
  ConsV ṽ₁ ṽ₂ → do
    si₁ :* cv₁ ← unShareValP ṽ₁
    si₂ :* cv₂ ← unShareValP ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* ConsCV cv₁ cv₂
  BulV → return $ NotShared :* BulCV
  UnknownV _τ → throwIErrorCxt InternalIError "unShareVal: UnknownV τ" $ frhs [ ("τ",pretty _τ) ]
  v → throwIErrorCxt NotImplementedIError "unShareVal" $ frhs
      [ ("v",pretty v) ]

unShareValPs ∷ (STACK) ⇒ 𝐿 ValP → IM (ShareInfo ∧ 𝐿 CktVal)
unShareValPs = mfoldrFromWith (NotShared :* null) $ \ ṽ (siᵢ :* cvs) → do
  si :* cv ← unShareValP ṽ
  si' ← joinShareInfo siᵢ si
  return $ si' :* (cv :& cvs)

reShareValP ∷ (STACK) ⇒ CktVal → ShareInfo → IM ValP
reShareValP cv = \case
  NotShared   → valPFrCktVal cv
  Shared φ ρs → reShareValPShared φ ρs cv

reShareValPShared ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → CktVal → IM ValP
reShareValPShared φ ρs = \case
  DefaultCV → introValP DefaultV
  BaseCV c → return $ ShareVP φ ρs $ BaseCV c
  PairCV cv₁ cv₂ → do
    ṽ₁ ← reShareValPShared φ ρs cv₁
    ṽ₂ ← reShareValPShared φ ρs cv₂
    introValP $ PairV ṽ₁ ṽ₂
  SumCV c₁ cv₂ cv₃ → return $ ShareVP φ ρs $ SumCV c₁ cv₂ cv₃
  NilCV → introValP NilV
  ConsCV cv₁ cv₂ → do
    ṽ₁ ← reShareValPShared φ ρs cv₁
    ṽ₂ ← reShareValPShared φ ρs cv₂
    introValP $ ConsV ṽ₁ ṽ₂
  BulCV → introValP BulV

valPFrCktVal ∷ (STACK) ⇒ CktVal → IM ValP
valPFrCktVal = \case
  DefaultCV → introValP DefaultV
  BaseCV c → valPFrCkt c
  PairCV cv₁ cv₂ → do
    ṽ₁ ← valPFrCktVal cv₁
    ṽ₂ ← valPFrCktVal cv₂
    introValP $ PairV ṽ₁ ṽ₂
  SumCV c₁ cv₂ cv₃ → do
    v₁ ← valPFrCkt c₁ ≫= elimValP
    b₁ ← error𝑂 (view boolVL v₁) (throwIErrorCxt TypeIError "valPFrCktVal: SumCV: view boolVL v₁ ≡ None" $ frhs
                                  [ ("v₁",pretty v₁)
                                  ])
    if b₁
    then do
      ṽ₂ ← valPFrCktVal cv₂
      introValP $ LV ṽ₂
    else do
      ṽ₃ ← valPFrCktVal cv₃
      introValP $ RV ṽ₃
  NilCV → introValP NilV
  ConsCV cv₁ cv₂ → do
    ṽ₁ ← valPFrCktVal cv₁
    ṽ₂ ← valPFrCktVal cv₂
    introValP $ ConsV ṽ₁ ṽ₂
  BulCV → introValP BulV

valPFrCkt ∷ (STACK) ⇒ Ckt → IM ValP
valPFrCkt ckt =
  let outW = outC ckt in
    case impLookup𝐷 (gatesC ckt) outW of
      BaseG bg    → valPFrBaseGate bg
      InputG _ i  → valPFrInput i
      PrimG op ws → do
        vs ← mapMOn ws $ \ w → do
          ṽ ← valPFrCkt $ ckt { outC = w }
          elimValP ṽ
        v' ← interpPrim op vs
        introValP v'

valPFrInput ∷ (STACK) ⇒ Input → IM ValP
valPFrInput = \case
  AvailableI bg → valPFrBaseGate bg
  UnavailableI τ → throwIErrorCxt InternalIError "valPFrInput: UnavailableI τ" $ frhs [ ("τ", pretty τ) ]

valPFrBaseGate ∷ (STACK) ⇒ BaseGate → IM ValP
valPFrBaseGate = \case
  BoolBG b → introValP $ BoolV b
  NatBG pr n → introValP $ NatV pr n
  IntBG pr i → introValP $ IntV pr i
  FltBG pr d → introValP $ FltV pr d
  PrinBG peO → case peO of
    BotBTD → introValP DefaultV
    AddBTD pe → introValP $ PrinV $ ValPEV pe
    TopBTD → introValP BulV

--TODO(ins): Ask David about these
prinFrPrinVal ∷ PrinVal → Prin
prinFrPrinVal (SinglePV p) = p
prinFrPrinVal (AccessPV p _) = p
prinFrPrinVal (VirtualPV p) = p

revealValP ∷ (STACK) ⇒ 𝑃 PrinVal → ValP → IM ValP
revealValP ρsʳ ṽ = case ṽ of
  AllVP v → revealVal ρsʳ v
  SSecVP ρs' v | ρsʳ ⊆ ρs' → revealVal ρsʳ v
  ShareVP _φ ρsˢ cv → do
    lm ← askL iCxtLocalModeL
    let frCktVal = if (SecM ρsˢ) ⊑ lm then valPFrCktVal else undefined -- TODO: actually run EMP
    restrictMode (SecM ρsʳ) $ restrictValP *$ frCktVal cv
  _ → throwIErrorCxt TypeIError "revealValP: Cannot reveal ṽ." $ frhs [ ("ρsʳ", pretty ρsʳ), ("ṽ", pretty ṽ) ]

revealVal ∷ (STACK) ⇒ 𝑃 PrinVal → Val → IM ValP
revealVal ρsʳ v = case v of
  BoolV b → introValP $ BoolV b
  StrV s → introValP $ StrV s
  NatV p n → introValP $ NatV p n
  IntV p i → introValP $ IntV p i
  FltV p f → introValP $ FltV p f
  BulV → introValP BulV
  PairV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ρsʳ ṽ₁
    ṽ₂' ← revealValP ρsʳ ṽ₂
    introValP $ PairV ṽ₁' ṽ₂'
  LV ṽ → do
    ṽ' ← revealValP ρsʳ ṽ
    introValP $ LV ṽ'
  RV ṽ → do
    ṽ' ← revealValP ρsʳ ṽ
    introValP $ RV ṽ'
  NilV → introValP NilV
  ConsV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ρsʳ ṽ₁
    ṽ₂' ← revealValP ρsʳ ṽ₂
    introValP $ ConsV ṽ₁' ṽ₂'
  PrinV pev → introValP $ PrinV pev
  PrinSetV pevs → introValP $ PrinSetV pevs
  LocV m ℓ → introValP $ LocV m ℓ
  DefaultV → introValP DefaultV
  _ → throwIErrorCxt TypeIError "revealVal: cannot reveal v." $ frhs [ ("ρsʳ", pretty ρsʳ), ("v", pretty v) ]
