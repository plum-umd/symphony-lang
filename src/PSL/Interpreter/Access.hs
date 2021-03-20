module PSL.Interpreter.Access where

import UVMHS
import AddToUVMHS

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Json ()
import PSL.Interpreter.Primitives
import PSL.Interpreter.Share
import PSL.Interpreter.Val

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
  BaseV _ → return v
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

shareValP ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → ValP → IM MPCVal
shareValP φ ρvsFrom ρvsTo = \case
  SSecVP ρs v → do
    guardErr (ρvsFrom ⊆ ρs) $ throwIErrorCxt TypeIError "shareValP: SSecVP: ¬ (SecM ρvsFrom) ⊑ ρs " $ frhs
      [ ("ρvsFrom",pretty ρvsFrom)
      , ("ρs",pretty ρs)
      ]
    shareVal φ ρvsFrom ρvsTo v
  ShareVP _φ _ρs _v̂ → throwIErrorCxt TypeIError "shareValP: ShareVP: cannot share a share." $ frhs
    [ ("_φ", pretty _φ)
    , ("_ρs", pretty _ρs)
    , ("_v̂", pretty _v̂)
    ]
  AllVP v → shareVal φ ρvsFrom ρvsTo v
  ṽ → throwIErrorCxt TypeIError "shareValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _,AllVP _}" $ frhs
    [ ("ṽ",pretty ṽ) ]

shareVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → IM MPCVal
shareVal φ ρvsFrom ρvsTo = \case
  BaseV (BoolBV b) →
    withProt φ $ \ p sp → do
    pv ← boolInput p ρvsFrom b
    return $ BaseMV $ Share sp pv
{-  NatV pr n → do
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
      ] -}

shareValType ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Type → IM MPCVal
shareValType φ ρvsFrom ρvsTo = \case
    τ | base τ →
        withProt φ $ \ p sp → do
        pv ← unkInput p ρvsFrom τ
        return $ BaseMV $ Share sp pv
    UnitT → return $ BulMV
{-    τ₁ :×: τ₂ → do
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
        ] -}

  where base 𝔹T = True
        base (ℕT _) = True
        base (ℤT _) = True
        base (𝔽T _) = True
        base ℙT = True
        base _ = False

revealValP ∷ (STACK) ⇒ 𝑃 PrinVal → ValP → IM ValP
revealValP ρsʳ ṽ = case ṽ of
  AllVP v → revealVal ρsʳ v
  SSecVP ρs' v | ρsʳ ⊆ ρs' → revealVal ρsʳ v
  ShareVP φ ρsˢ v̂ → undefined
  _ → throwIErrorCxt TypeIError "revealValP: Cannot reveal ṽ." $ frhs [ ("ρsʳ", pretty ρsʳ), ("ṽ", pretty ṽ) ]

revealVal ∷ (STACK) ⇒ 𝑃 PrinVal → Val → IM ValP
revealVal ρsʳ v = case v of
  BaseV bv → valPFrVal $ BaseV bv
  PairV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ρsʳ ṽ₁
    ṽ₂' ← revealValP ρsʳ ṽ₂
    valPFrVal $ PairV ṽ₁' ṽ₂'
  LV ṽ → do
    ṽ' ← revealValP ρsʳ ṽ
    valPFrVal $ LV ṽ'
  RV ṽ → do
    ṽ' ← revealValP ρsʳ ṽ
    valPFrVal $ RV ṽ'
  NilV → valPFrVal NilV
  ConsV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ρsʳ ṽ₁
    ṽ₂' ← revealValP ρsʳ ṽ₂
    valPFrVal $ ConsV ṽ₁' ṽ₂'
  PrinSetV pevs → valPFrVal $ PrinSetV pevs
  LocV m ℓ → valPFrVal $ LocV m ℓ
  DefaultV → valPFrVal DefaultV
  _ → throwIErrorCxt TypeIError "revealVal: cannot reveal v." $ frhs [ ("ρsʳ", pretty ρsʳ), ("v", pretty v) ]
