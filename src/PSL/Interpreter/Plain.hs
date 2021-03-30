module PSL.Interpreter.Plain where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Error
import PSL.Interpreter.Lens
import PSL.Interpreter.Primitives
import PSL.Interpreter.Pretty ()

instance Protocol 'PlainP where
  type ProtocolVal 'PlainP = BaseVal

  typeOf ∷ P 'PlainP → BaseVal → BaseType
  typeOf _p = typeOfBaseVal

  shareBaseVal ∷ P 'PlainP → 𝑃 PrinVal → PrinVal → BaseVal → IM BaseVal
  shareBaseVal _p _ρvs _ρv = return

  shareUnk ∷ P 'PlainP → 𝑃 PrinVal → PrinVal → BaseType → IM BaseVal
  shareUnk _p _ρvs _ρv _bτ = throwIErrorCxt NotImplementedIError "[PlainP] exeUnk: TODO" empty𝐿

  embedBaseVal ∷ P 'PlainP → 𝑃 PrinVal → BaseVal → IM BaseVal
  embedBaseVal _p _ρvs = return

  exePrim ∷ P 'PlainP → 𝑃 PrinVal → Op → 𝐿 BaseVal → IM BaseVal
  exePrim _p _ρvs = interpPrim

  reveal ∷ P 'PlainP → 𝑃 PrinVal → 𝑃 PrinVal → MPCVal 'PlainP → IM Val
  reveal p ρvs₁ ρvs₂ v̂ =
    let toValP = SSecVP (SecM ρvs₂) in
    case v̂ of
      DefaultMV    → return DefaultV
      BulMV        → return BulV
      BaseMV bv    → return $ BaseV bv
      PairMV v̂₁ v̂₂ → do
        v₁ ← reveal p ρvs₁ ρvs₂ v̂₁
        v₂ ← reveal p ρvs₁ ρvs₂ v̂₂
        return $ PairV (toValP v₁) (toValP v₂)
      SumMV bv₁ v̂₂ v̂₃ → do
        b₁ ← error𝑂 (view boolBVL bv₁) (throwIErrorCxt TypeIError "reveal: (view boolBVL bv₁) ≡ None" $ frhs
                                        [ ("bv₁", pretty bv₁)
                                        ])
        let inj :* v = if b₁ then LV :* (reveal p ρvs₁ ρvs₂ v̂₂) else RV :* (reveal p ρvs₁ ρvs₂ v̂₃)
        map (inj ∘ toValP) v
