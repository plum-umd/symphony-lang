module PSL.Interpreter.Access where

import UVMHS

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Json

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

-- create a location fixed to the current mode
locValP ∷ (STACK) ⇒ ℤ64 → IM ValP
locValP ℓ = do
  m ← askL iCxtModeL
  return $ LocVP m ℓ

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
    PairVP ṽ₁ ṽ₂ → return $ PairV ṽ₁ ṽ₂
    LocVP m' ℓ → do
      guardErr (m ≡ m') $
        throwIErrorCxt TypeIError "elimValP: m ≠ m'" $ frhs
          [ ("m",pretty m)
          , ("m'",pretty m')
          ]
      return $ LocV ℓ
    _ → throwIErrorCxt TypeIError "elimValP: ṽ ∉ {AllVP _,SSecVP _ _,PairVP _ _,LocVP _ _}" $ frhs
        [ ("ṽ",pretty ṽ)
        ]

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
    (_,PairVP ṽ₁ ṽ₂) → do
      ṽ₁' ← restrictValP ṽ₁
      ṽ₂' ← restrictValP ṽ₂
      return $ PairVP ṽ₁' ṽ₂'
    (_,LocVP m' _) | m ≡ m' → return ṽ
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
    _ → throwIErrorCxt TypeIError "restrictValP: Pattern match fail on (m,ṽ)" $ frhs
        [ ("m",pretty m)
        , ("ṽ",pretty ṽ)
        ]

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
  LocV _ → return v
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

unShareValP ∷ (STACK) ⇒ ValP → IM (ShareInfo ∧ ValMPC)
unShareValP ṽ = do
  m ← askL iCxtModeL
  unShareValPMode m ṽ

unShareValPMode ∷ (STACK) ⇒ Mode → ValP → IM (ShareInfo ∧ ValMPC)
unShareValPMode m = \case
  SSecVP ρs v → do
    guardErr (m ⊑ SecM ρs) $ throwIErrorCxt TypeIError "bad" null
    unShareValMode m v
  ShareVP φ ρs vmpc → do
    guardErr (SecM ρs ⊑ m) $ throwIErrorCxt TypeIError "bad" null
    return $ (Shared φ ρs) :* vmpc
  AllVP v → do
    unShareValMode m v
  PairVP ṽ₁ ṽ₂ → do
    si₁ :* vmpc₁ ← unShareValPMode m ṽ₁
    si₂ :* vmpc₂ ← unShareValPMode m ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* PairMV vmpc₁ vmpc₂
  ISecVP _ → throwIErrorCxt TypeIError "bad" null
  LocVP _ _ → throwIErrorCxt TypeIError "bad" null
  UnknownVP → throwIErrorCxt TypeIError "bad" null

unShareValMode ∷ (STACK) ⇒ Mode → Val → IM (ShareInfo ∧ ValMPC)
unShareValMode m = \case
  BoolV b → return $ NotShared :* BaseMV 0 (BoolMV b)
  NatV pr n → return $ NotShared :* BaseMV 0 (NatMV pr n)
  IntV pr i → return $ NotShared :* BaseMV 0 (IntMV pr i)
  FltV pr i → return $ NotShared :* BaseMV 0 (FltMV pr i)
  PrinV (ValPEV ρe) → return $ NotShared :* BaseMV 0 (PrinMV ρe)
  PairV ṽ₁ ṽ₂ → do
    si₁ :* vmpc₁ ← unShareValPMode m ṽ₁
    si₂ :* vmpc₂ ← unShareValPMode m ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* PairMV vmpc₁ vmpc₂
  LV ṽ → do
    si :* vmpc ← unShareValPMode m ṽ
    return $ si :* SumMV zero False vmpc DefaultMV
  RV ṽ → do
    si :* vmpc ← unShareValPMode m ṽ
    return $ si :* SumMV zero True DefaultMV vmpc
  NilV → return $ NotShared :* NilMV
  ConsV ṽ₁ ṽ₂ → do
    si₁ :* vmpc₁ ← unShareValPMode m ṽ₁
    si₂ :* vmpc₂ ← unShareValPMode m ṽ₂
    si ← joinShareInfo si₁ si₂
    return $ si :* ConsMV vmpc₁ vmpc₂
  DefaultV → return $ NotShared :* DefaultMV
  v → throwIErrorCxt NotImplementedIError "unShareValMode" $ frhs
    [ ("v",pretty v) ]

unShareValPs ∷ (STACK) ⇒ 𝐿 ValP → IM (ShareInfo ∧ 𝐿 ValMPC)
unShareValPs = mfoldrFromWith (NotShared :* null) $ \ ṽ (siᵢ :* vmpcs) → do
  si :* vmpc ← unShareValP ṽ
  si' ← joinShareInfo siᵢ si
  return $ si' :* (vmpc :& vmpcs)

reShareValP ∷ (STACK) ⇒ ValMPC → ShareInfo → IM ValP
reShareValP ṽ = \case
  NotShared → valFrMPC ṽ
  Shared φ ρs → reShareValPShared φ ρs ṽ

reShareValPShared ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ValMPC → IM ValP
reShareValPShared φ ρs = \case
  BaseMV md bvmpc → return $ ShareVP φ ρs $ BaseMV md bvmpc
  PairMV vmpc₁ vmpc₂ → do
    ṽ₁ ← reShareValPShared φ ρs vmpc₁
    ṽ₂ ← reShareValPShared φ ρs vmpc₂
    return $ PairVP ṽ₁ ṽ₂
  SumMV md b vmpc₁ vmpc₂ → return $ ShareVP φ ρs $ SumMV md b vmpc₁ vmpc₂
  NilMV → introValP NilV
  ConsMV vmpc₁ vmpc₂ → do
    ṽ₁ ← reShareValPShared φ ρs vmpc₁
    ṽ₂ ← reShareValPShared φ ρs vmpc₂
    introValP $ ConsV ṽ₁ ṽ₂
  DefaultMV → introValP DefaultV

----------------
-- MPC VALUES --
----------------

mpcFrValF ∷ (STACK) ⇒ Val → (BaseValMPC → IM ()) → IM ValMPC
mpcFrValF = flip mpcFrValFWith

mpcFrValFWith ∷ (STACK) ⇒ (BaseValMPC → IM ()) → Val → IM ValMPC
mpcFrValFWith f = \case
  BoolV b → do
    let bvmpc = BoolMV b
    f bvmpc
    return $ BaseMV zero bvmpc
  NatV pr n → do
    let bvmpc = NatMV pr n
    f bvmpc
    return $ BaseMV zero bvmpc
  IntV pr i → do
    let bvmpc = IntMV pr i
    f bvmpc
    return $ BaseMV zero bvmpc
  FltV pr i → do
    let bvmpc = FltMV pr i
    f bvmpc
    return $ BaseMV zero bvmpc
  PrinV (ValPEV ρe) → return $ BaseMV zero $ PrinMV ρe
  PairV ṽ₁ ṽ₂ → do
    vmpc₁ ← mpcFrValFWith f *$ elimValP ṽ₁
    vmpc₂ ← mpcFrValFWith f *$ elimValP ṽ₂
    return $ PairMV vmpc₁ vmpc₂
  LV ṽ → do
    vmpc ← mpcFrValFWith f *$ elimValP ṽ
    return $ SumMV zero False vmpc DefaultMV
  RV ṽ → do
    v ← elimValP ṽ
    vmpc ← mpcFrValFWith f v
    return $ SumMV zero True DefaultMV vmpc
  NilV → return $ NilMV
  ConsV ṽ₁ ṽ₂ → do
    vmpc₁ ← mpcFrValFWith f *$ elimValP ṽ₁
    vmpc₂ ← mpcFrValFWith f *$ elimValP ṽ₂
    return $ ConsMV vmpc₁ vmpc₂
  _ → throwIErrorCxt TypeIError "bad" null

mpcFrVal ∷ (STACK) ⇒ Val → IM ValMPC
mpcFrVal = mpcFrValFWith $ const skip

valFrMPC ∷ (STACK) ⇒ ValMPC → IM ValP
valFrMPC = valFrMPCFWith $ const $ const skip

valFrMPCF ∷ (STACK) ⇒ ValMPC → (ℕ → BaseValMPC → IM ()) → IM ValP
valFrMPCF = flip valFrMPCFWith

valFrMPCFWith ∷ (STACK) ⇒ (ℕ → BaseValMPC → IM ()) → ValMPC → IM ValP
valFrMPCFWith f = \case
  BaseMV md bvmpc → do
    f md bvmpc
    ṽ ← valFrBaseMPC bvmpc
    return $ ṽ
  PairMV vmpc₁ vmpc₂ → do
    ṽ₁ ← valFrMPCF vmpc₁ f
    ṽ₂ ← valFrMPCF vmpc₂ f
    return $ PairVP ṽ₁ ṽ₂
  SumMV md b vmpc₁ vmpc₂ → do
    f md (BoolMV b)
    if b
    then do
      ṽ ← valFrMPCF vmpc₁ f
      ṽ' ← introValP $ LV ṽ
      return ṽ'
    else do
      ṽ ← valFrMPCF vmpc₂ f
      ṽ' ← introValP $ RV ṽ
      return ṽ'
  _ → error "TODO: not implemented"

valFrBaseMPC ∷ (STACK) ⇒ BaseValMPC → IM ValP
valFrBaseMPC = \case
  BoolMV b → introValP $ BoolV b
  NatMV pr n → introValP $ NatV pr n
  IntMV pr i → introValP $ IntV pr i
  FltMV pr d → introValP $ FltV pr d
  PrinMV pe → introValP $ PrinV $ ValPEV pe

revealValP ∷ (STACK) ⇒ 𝑃 PrinVal → ValP → IM ValP
revealValP ρsʳ = \case
  AllVP v → revealVal ρsʳ v
  SSecVP ρs' v | ρsʳ ⊆ ρs' → revealVal ρsʳ v
  ShareVP φ ρsˢ vmpc → restrictMode (SecM ρsʳ) $ restrictValP *$ valFrMPCF vmpc $ \ md bvmpc → 
    tellL iOutResEvsL $ ResEv φ pø ρsˢ ρsʳ (getTypeBaseMPC  bvmpc) "REVEAL" md ↦ 1
  PairVP ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ρsʳ ṽ₁
    ṽ₂' ← revealValP ρsʳ ṽ₂
    return $ PairVP ṽ₁' ṽ₂'
  LocVP m ℓ | SecM ρsʳ ⊑ m → return $ LocVP m ℓ
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
    return $ PairVP ṽ₁' ṽ₂'
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
  LocV ℓ → introValP $ LocV ℓ
  DefaultV → introValP DefaultV
  v → throwIErrorCxt TypeIError "can't reveal" $ frhs
    [ ("v",pretty v) ]
