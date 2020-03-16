module PSL.Interpreter.Access where

import UVMHS

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

-----------
-- MODES --
-----------

-- enter a strictly smaller mode than the current one
restrictMode ∷ (STACK) ⇒ Mode → IM a → IM a
restrictMode m' xM = do
  m ← askL iCxtModeL
  when (not $ m' ⊑ m) $ \ _ → throwIErrorCxt TypeIError "m' ⋢ m" $ frhs
    [ ("m'",pretty m')
    , ("m",pretty m)
    ]
  localL iCxtModeL m' xM

---------------------
-- PARALLEL VALUES --
---------------------

-- inject a value into a mode
modeValP ∷ (STACK) ⇒ Mode → Val → ValP
modeValP m v = case m of
  SecM ρ → SSecVP (single ρ) v
  PSecM ρs → SSecVP ρs v
  TopM → AllVP v

-- create a value known to current mode
introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  m ← askL iCxtModeL
  return $ modeValP m v

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
      guardErr (m ⊑ PSecM ρs) (throwIErrorCxt TypeIError "elimValP: m ⋢ PSecM ρs" $ frhs
                               [ ("m",pretty m)
                               , ("ρs",pretty ρs)
                               ])
      return v'
    AllVP v' → return v'
    _ → throwIErrorCxt TypeIError "elimValP: ṽ ∉ {AllVP _,SSecVP _ _}" $ frhs
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
    (SecM ρ, SSecVP ρs v) → do
      v' ← restrictValPRecVal v
      return $ SSecVP (single ρ ∩ ρs) v'
    (SecM ρ, ISecVP ρvs) → do
      v ← error𝑂 (ρvs ⋕? ρ) (throwIErrorCxt TypeIError "restrictValP: ρ not in ρvs" $ frhs
                             [ ("ρvs",pretty ρvs)
                             , ("ρ",pretty ρ)
                             ])
      return $ SSecVP (single ρ) v
    (SecM ρ, AllVP v) → do
      v' ← restrictValPRecVal v
      return $ SSecVP (single ρ) v'
    (PSecM ρs₁, SSecVP ρs₂ v) → do
      v' ← restrictValPRecVal v
      let ρs = ρs₁ ∩ ρs₂
      return $ SSecVP ρs v'
    (PSecM ρs, ISecVP ρvs) → do
      let ρvs' = restrict ρs ρvs
      return $ ISecVP ρvs'
    (PSecM ρs₁, ShareVP φ ρs₂ {- md -} v) → do
      guardErr (ρs₂ ⊆ ρs₁) (throwIErrorCxt TypeIError "restrictValP: ρs₁ ⊈ ρs₂" $ frhs
                            [ ("ρs₁",pretty ρs₁)
                            , ("ρs₂",pretty ρs₂)
                            ])
      return $ ShareVP φ ρs₂ {- md -} v
    (PSecM ρs, AllVP v) → do
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
    v ← restrictValP ṽ
    return $ LV v
  RV ṽ → do
    v ← restrictValP ṽ
    return $ RV v
  PairV ṽ₁ ṽ₂ → do
    v₁ ← restrictValP ṽ₁
    v₂ ← restrictValP ṽ₂
    return $ PairV v₁ v₂
  NilV → return v
  ConsV ṽ₁ ṽ₂ → do
    v₁ ← restrictValP ṽ₁
    v₂ ← restrictValP ṽ₂
    return $ ConsV v₁ v₂
  ConsV _ _ → return v
  CloV _ _ _ _  → return v
  TCloV _ _ _ → return v
  PrinV _ → return v
  PrinSetV _ → return v

unShareValPsMode ∷ Mode → 𝐿 ValP → 𝑂 (𝐿 Val ∧ 𝑂 (Prot ∧ 𝑃 PrinVal {- ∧ ℕ -}))
unShareValPsMode m ṽs = case ṽs of
  Nil → return $ Nil :* None
  ṽ :& ṽs' → do
    (v,φρsO₁) ← case ṽ of
      SSecVP ρs v → do
        guard $ m ⊑ PSecM ρs
        return (v,None)
      ShareVP φ ρs {- md -} v → do
        guard $ PSecM ρs ⊑ m
        return (valFrMPC v,Some $ φ :* ρs {- :* md -})
      AllVP v → return (v,None)
      ISecVP _ → abort
    vs :* φρsO₂ ← unShareValPsMode m ṽs'
    φρsO ← case (φρsO₁,φρsO₂) of
      (None,_) → return φρsO₂
      (_,None) → return φρsO₁
      (Some (φ₁ :* ρs₁ {- :* md₁ -}),Some (φ₂ :* ρs₂ {- :* md₂ -})) → do
        guard $ φ₁ ≡ φ₂
        guard $ ρs₁ ≡ ρs₂
        return $ Some $ φ₁ :* ρs₁ {- :* (md₁ ⊔ md₂) -}
    return $ (v :& vs) :* φρsO

unShareValPs ∷ 𝐿 ValP → IM (𝐿 Val ∧ 𝑂 (Prot ∧ 𝑃 PrinVal {- ∧ ℕ -}))
unShareValPs ṽs = do
  m ← askL iCxtModeL
  vsφρsO ← error𝑂 (unShareValPsMode m ṽs) (throwIErrorCxt TypeIError "unShareValsPs" $ frhs
                                           [ ("ṽs",pretty ṽs)
                                           ])
  return vsφρsO

reShareValP ∷ 𝑂 (Prot ∧ 𝑃 PrinVal {- ∧ ℕ -}) → Val → IM ValP
reShareValP φρsO v =case φρsO of
  None → introValP v
  Some (φ :* ρs {- :* md -}) → do
    sv ← mpcFrVal v
    return $ ShareVP φ ρs {- md -} sv

----------------
-- MPC VALUES --
----------------

mpcFrVal ∷ (STACK) ⇒ Val → IM ValMPC
mpcFrVal v = case v of
  BoolV b → return $ BoolMV b
  NatV pr n → return $ NatMV pr n
  IntV pr i → return $ IntMV pr i
  FltV pr i → return $ FltMV pr i
  PrinV ρe → return $ PrinMV ρe
  PrinSetV ρs → return $ PrinMV $ PowPEV ρs
  _ → throwIErrorCxt TypeIError "mpcFrVal: v ∉ BoolV,NatV,IntV,FltV,PrinV" $ frhs
    [ ("v",pretty v)
    ]

valFrMPC ∷ (STACK) ⇒ ValMPC → Val
valFrMPC = \case
  BoolMV b → BoolV b
  NatMV pr n → NatV pr n
  IntMV pr i → IntV pr i
  FltMV pr d → FltV pr d
  PrinMV pe → PrinV pe
  -- PairMV v₁ v₂ → PairV (valFrMCP v₁) $ valFrMPC v₂

