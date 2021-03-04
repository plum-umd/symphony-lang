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
  m ← askL iCxtModeL
  when (not $ m' ⊑ m) $ \ _ → throwIErrorCxt TypeIError "m' ⋢ m" $ frhs
    [ ("m'",pretty m')
    , ("m",pretty m)
    ]
  localL iCxtModeL m' xM

-- create a value known to current mode
introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  m ← askL iCxtModeL
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
  m ← askL iCxtModeL
  case ṽ of
    SSecVP ρs v' → do
      guardErr (m ⊑ SecM ρs) $
        throwIErrorCxt TypeIError "elimValP: m ⋢ PSecM ρs" $ frhs
          [ ("m",pretty m)
          , ("ρs",pretty ρs)
          ]
      return v'
    AllVP v' → return v'
    -- LocVP m' ℓ → do
    --   guardErr (m ≡ m') $
    --     throwIErrorCxt TypeIError "elimValP: m ≠ m'" $ frhs
    --       [ ("m",pretty m)
    --       , ("m'",pretty m')
    --       ]
    --   return $ LocV ℓ
    _ → throwIErrorCxt TypeIError "elimValP: ṽ ∉ {AllVP _,SSecVP _ _,LocVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]

-- create a location fixed to the current mode
introLocV ∷ (STACK) ⇒ ℤ64 → IM Val
introLocV ℓ = do
  m ← askL iCxtModeL
  return $ LocV m ℓ

elimLocV ∷ (STACK) ⇒ Val → IM ℤ64
elimLocV v = do
  m ← askL iCxtModeL
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

-- restrict the mode on a value to be no larger than execution mode
-- e.g.:
-- ‣ if current mode is {par:A,B} and value is {ssec:C} this fails
-- ‣ if current mode is {par:A,B} and value is {ssec:A}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B,C}, this succeeds with value in {ssec:A,B}
restrictValP ∷ (STACK) ⇒ ValP → IM ValP
restrictValP ṽ = do
  m ← askL iCxtModeL
  case (m,ṽ) of
    -- (_,LocVP m' _) | m ≡ m' → return ṽ
    (SecM ρs₁, SSecVP ρs₂ v) → do
      v' ← restrictValPRecVal v
      let ρs = ρs₁ ∩ ρs₂
      return $ SSecVP ρs v'
    (SecM ρs, ISecVP ρvs) → do
      let ρvs' = restrict ρs ρvs
      return $ ISecVP ρvs'
    (SecM ρs₁, ShareVP φ ρs₂ v) → do
      guardErr (ρs₂ ⊆ ρs₁) (throwIErrorCxt TypeIError "restrictValP: ρs₂ ⊈ ρs₁" $ frhs
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
  DefaultV → return DefaultV

joinShareInfo ∷ (STACK) ⇒ ShareInfo → ShareInfo → IM ShareInfo
joinShareInfo si₁ si₂ = case (si₁,si₂) of
  (NotShared,_) → return si₂
  (_,NotShared) → return si₁
  (Shared φ₁ ρs₁,Shared φ₂ ρs₂)
    | (φ₁ ≡ φ₂) ⩓ (ρs₁ ≡ ρs₂) → return $ Shared φ₁ ρs₁
  _ → throwIErrorCxt TypeIError "bad" null

joinShareInfos ∷ (STACK,ToIter ShareInfo t) ⇒ t → IM ShareInfo
joinShareInfos = mfoldFromWith NotShared joinShareInfo

unShareValP ∷ (STACK) ⇒ ValP → IM (ShareInfo ∧ CktVal)
unShareValP ṽ = do
  m ← askL iCxtModeL
  unShareValPMode m ṽ

unShareValPMode ∷ (STACK) ⇒ Mode → ValP → IM (ShareInfo ∧ CktVal)
unShareValPMode m = \case
  SSecVP ρs v → do
    guardErr (m ⊑ SecM ρs) $
      throwIErrorCxt TypeIError "unShareValPMode: SSecVP: ¬ m ⊑ SecM ρs " $ frhs
        [ ("m",pretty m)
        , ("ρs",pretty ρs)
        ]
    unShareValMode m v
  ShareVP φ ρs cv → return $ (Shared φ ρs) :* cv
  AllVP v → do
    unShareValMode m v
  ṽ → throwIErrorCxt TypeIError
    "unShareValPMode: ṽ ∉ {SSecVP _ _,ShareVP _ _ _,AllVP _}" $ frhs
      [ ("ṽ",pretty ṽ) ]

unShareValMode ∷ (STACK) ⇒ Mode → Val → IM (ShareInfo ∧ CktVal)
unShareValMode m = \case
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
    si₁ :* cv₁ ← unShareValPMode m ṽ₁
    si₂ :* cv₂ ← unShareValPMode m ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* PairCV cv₁ cv₂
  LV ṽ → do
    si :* cv ← unShareValPMode m ṽ
    left ← trueCkt
    return $ si :* SumCV left cv DefaultCV
  RV ṽ → do
    si :* cv ← unShareValPMode m ṽ
    right ← falseCkt
    return $ si :* SumCV right DefaultCV cv
  NilV → return $ NotShared :* NilCV
  ConsV ṽ₁ ṽ₂ → do
    si₁ :* cv₁ ← unShareValPMode m ṽ₁
    si₂ :* cv₂ ← unShareValPMode m ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* ConsCV cv₁ cv₂
  BulV → return $ NotShared :* BulCV
  UnknownV ρvs τ → do
    c ← inputCkt ρvs τ
    return $ NotShared :* BaseCV c
  v → throwIErrorCxt NotImplementedIError "unShareValMode" $ frhs
    [ ("v",pretty v) ]

unShareValPs ∷ (STACK) ⇒ 𝐿 ValP → IM (ShareInfo ∧ 𝐿 CktVal)
unShareValPs = mfoldrFromWith (NotShared :* null) $ \ ṽ (siᵢ :* cvs) → do
  si :* cv ← unShareValP ṽ
  si' ← joinShareInfo siᵢ si
  return $ si' :* (cv :& cvs)

reShareValP ∷ (STACK) ⇒ CktVal → ShareInfo → IM ValP
reShareValP cv = \case
  NotShared   → valPFrCktVal cv
  Shared φ ρs → return $ ShareVP φ ρs cv

valPFrCktVal ∷ (STACK) ⇒ CktVal → IM ValP
valPFrCktVal = \case
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

valPFrCkt ∷ (STACK) ⇒ Ckt → IM ValP
valPFrCkt ckt =
  assert (inputs ckt ≡ empty𝐿) $ -- Sanity check, unshared circuits cannot have inputs
  case impLookup𝐷 (gates ckt) (output ckt) of
    BaseG bc → valPFrBaseCkt bc
    PrimG op ws → do
      vs ← mapMOn ws $ \ w → do
        vps ← valPFrCkt $ ckt { output = w }
        elimValP vps
      v' ← interpPrim op vs
      introValP v'

{-
  BaseC bc → do
    ṽ ← valFrBaseCkt bc
    return $ ṽ
  PairC c₁ c₂ → do
    ṽ₁ ← valFrCkt c₁
    ṽ₂ ← valFrCkt c₂
    introValP $ PairV ṽ₁ ṽ₂
  SumC b c₁ c₂ → do
    if b
    then do
      ṽ ← valFrCkt c₁
      ṽ' ← introValP $ LV ṽ
      return ṽ'
    else do
      ṽ ← valFrCkt c₂
      ṽ' ← introValP $ RV ṽ
      return ṽ'
  DefaultC → introValP DefaultV -}

valPFrBaseCkt ∷ (STACK) ⇒ BaseCkt → IM ValP
valPFrBaseCkt = \case
  BoolBC b → introValP $ BoolV b
  NatBC pr n → introValP $ NatV pr n
  IntBC pr i → introValP $ IntV pr i
  FltBC pr d → introValP $ FltV pr d
  PrinBC peO → case peO of
    BotBTD → introValP DefaultV
    AddBTD pe → introValP $ PrinV $ ValPEV pe
    TopBTD → introValP BulV

--TODO(ins): Ask David about these
prinFrPrinVal ∷ PrinVal → Prin
prinFrPrinVal (SinglePV p) = p
prinFrPrinVal (AccessPV p _) = p
prinFrPrinVal (VirtualPV p) = p

revealValP ∷ (STACK) ⇒ 𝑃 PrinVal → ValP → IM ValP
revealValP ρsʳ ṽ = do
  _si :* cv ← unShareValP ṽ
  reShareValP cv NotShared

  {-throwIErrorCxt NotImplementedIError "revealValP" $ frhs
                 [ ("ρsʳ", pretty ρsʳ)
                 , ("ṽ", pretty ṽ)
                 ] -- where the magic happens (compile circuit and send to EMP) -}

{-

revealBaseValMPC ∷ (STACK) ⇒ 𝑃 PrinVal → BaseValMPC → IM ValP
revealBaseValMPC ρs = \case
  BoolMV b → introValP $ BoolV b
  NatMV pr n → introValP $ NatV pr n
  IntMV pr (IntSeqSh i) → introValP $ IntV pr i
  IntMV pr (IntEMPSh i) → do
    z ← integerReveal i (pmap prinFrPrinVal ρs)
    introValP $ IntV pr z
  FltMV pr d → introValP $ FltV pr d
  PrinMV peO → case peO of
    BotBTD → introValP DefaultV
    AddBTD pe → introValP $ PrinV $ ValPEV pe
    TopBTD → introValP BulV

revealValMPC ∷ (STACK) ⇒ 𝑃 PrinVal → ValMPC → IM ValP
revealValMPC ρs = \case
  BaseMV bvmpc → revealBaseValMPC ρs bvmpc
  PairMV vmpc₁ vmpc₂ → do
    ṽ₁ ← revealValMPC ρs vmpc₁
    ṽ₂ ← revealValMPC ρs vmpc₂
    introValP $ PairV ṽ₁ ṽ₂
  SumMV b vmpc₁ vmpc₂ → do
    if b
    then do
      ṽ ← revealValMPC ρs vmpc₁
      ṽ' ← introValP $ LV ṽ
      return ṽ'
    else do
      ṽ ← revealValMPC ρs vmpc₂
      ṽ' ← introValP $ RV ṽ
      return ṽ'
  NilMV → introValP NilV
  ConsMV vmpc₁ vmpc₂ → do
    ṽ₁ ← revealValMPC ρs vmpc₁
    ṽ₂ ← revealValMPC ρs vmpc₂
    introValP $ ConsV ṽ₁ ṽ₂
  BulMV → introValP BulV
  DefaultMV → introValP DefaultV

revealValP ∷ (STACK) ⇒ 𝑃 PrinVal → ValP → IM ValP
revealValP ρsʳ = \case
  AllVP v → revealVal ρsʳ v
  SSecVP ρs' v | ρsʳ ⊆ ρs' → revealVal ρsʳ v --TODO(ins): verify that these checks are correct
  ShareVP _ _ vmpc → revealValMPC ρsʳ vmpc
  ṽ → throwIErrorCxt TypeIError "can't reveal" $ frhs
    [ ("ṽ",pretty ṽ) ]

revealVal ∷ (STACK) ⇒ 𝑃 PrinVal → Val → IM ValP
revealVal ρsʳ = \case
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
  v → throwIErrorCxt TypeIError "can't reveal" $ frhs
    [ ("v",pretty v) ]

-}
