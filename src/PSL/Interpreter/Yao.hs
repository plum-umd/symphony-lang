module PSL.Interpreter.Yao where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Truncating

import PSL.Interpreter.EMP

import qualified Prelude as HS

instance Protocol 'Yao2P where
  type ProtocolVal 'Yao2P = EMPVal

  typeOf ∷ P 'Yao2P → EMPVal → BaseType
  typeOf _p = empType

  shareBaseVal ∷ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseVal → IM EMPVal
  shareBaseVal _p ρvs ρv bv = do
    pptraceM "sharing..."
    pptraceM bv
    empShare ρvs (single ρv) bv

  shareUnk ∷ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseType → IM EMPVal
  shareUnk p ρvs ρv bτ = do
    pptraceM "sharing..."
    pptraceM bτ
    empShare ρvs (single ρv) (defaultBaseValOf bτ)

  embedBaseVal ∷ P 'Yao2P → 𝑃 PrinVal → BaseVal → IM EMPVal
  embedBaseVal _p ρvs bv = empShare ρvs ρvs bv

  exePrim ∷ P 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → IM EMPVal
  exePrim _p ρvs op evs = case (op, tohs evs) of
    (NotO, [ BoolEV eb₁ ]) → map BoolEV $ io $ empBitNot eb₁
    (CondO, [ BoolEV eb₁, BoolEV eb₂, BoolEV eb₃ ]) → map BoolEV $ io $ empBitCond eb₁ eb₂ eb₃
    (PlusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerAdd ez₁ ez₂
    (MinusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerSub ez₁ ez₂
    (TimesO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMult ez₁ ez₂
    (DivO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerDiv ez₁ ez₂
    (EqO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerEq ez₁ ez₂
    (CondO, [ BoolEV eb₁, IntEV pr₁ ez₁, IntEV pr₂ ez₂]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerCond eb₁ ez₁ ez₂
    (PlusO, [ NatEV pr₁ en₁, NatEV pr₂ en₂ ]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerAdd en₁ en₂
    (CondO, [ BoolEV eb₁, NatEV pr₁ en₁, NatEV pr₂ en₂]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerCond eb₁ en₁ en₂
    _ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("op", pretty op), ("evs", pretty evs) ]

  reveal ∷ P 'Yao2P → 𝑃 PrinVal → 𝑃 PrinVal → MPCVal 'Yao2P → IM Val
  reveal _p ρvs₁ ρvs₂ = \case
    BaseMV (IntEV pr ez) → map (BaseV ∘ (IntBV pr) ∘ (trPrInt pr)) $ empIntegerReveal ez ρvs₂
    BaseMV (NatEV pr en) → map (BaseV ∘ (NatBV pr) ∘ (trPrNat pr) ∘ HS.fromIntegral) $ empIntegerReveal en ρvs₂
