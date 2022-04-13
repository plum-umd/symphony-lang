module Symphony.Interpreter.BaseVal.Operations where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Interpreter.Lens
import Symphony.Interpreter.Types
import Symphony.Interpreter.Error
import Symphony.Interpreter.BaseVal.Types

-------------------------
--- Elimination Forms ---
-------------------------

introClear ∷ (STACK) ⇒ ClearBaseVal → IM v (BaseVal e)
introClear cbv = return $ Clear cbv

elimClear ∷ (STACK) ⇒ BaseVal e → IM v ClearBaseVal
elimClear = \case
  Clear cbv             → return cbv
  Encrypted _φ _ρ𝑃 _ebv → throwIErrorCxt TypeIError "elimClear: E" empty𝐿

elimEncrypted ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → BaseVal e → IM v e
elimEncrypted φₑ ρsₑ = \case
  Clear _cbv           → throwIErrorCxt TypeIError "elimEncrypted: C" empty𝐿
  Encrypted φₐ ρsₐ ebv → do
    guardErr (φₑ ≡ φₐ ⩓ ρsₑ ≡ ρsₐ) $
      throwIErrorCxt TypeIError "elimEncrypted: φₑ ≢ φₐ ⩔ ρvsₑ ≢ ρvsₐ" $ frhs
      [ ("φₑ", pretty φₑ)
      , ("φₐ", pretty φₐ)
      , ("ρvsₑ", pretty ρsₑ)
      , ("ρvsₐ", pretty ρsₐ)
      ]
    return ebv

elimPrin ∷ (STACK) ⇒ ClearBaseVal → IM v PrinVal
elimPrin cbv = error𝑂 (view prinVL cbv) $
               throwIErrorCxt TypeIError "elimPrin: view prinVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimPrinSet ∷ (STACK) ⇒ ClearBaseVal → IM v PrinSetVal
elimPrinSet cbv = error𝑂 (view prinSetVL cbv) $
                  throwIErrorCxt TypeIError "elimPrinSet: view prinSetVL cbv ≡ None" $ frhs
                  [ ("cbv", pretty cbv)
                  ]

elimBool ∷ (STACK) ⇒ ClearBaseVal → IM v 𝔹
elimBool cbv = error𝑂 (view boolVL cbv) $
               throwIErrorCxt TypeIError "elimBool: view boolVL cbv ≡ None" $ frhs
               [ ("cbv", pretty cbv)
               ]

elimNat ∷ (STACK) ⇒ ClearBaseVal → IM v (IPrecision ∧ ℕ)
elimNat cbv = error𝑂 (view natVL cbv) $
              throwIErrorCxt TypeIError "elimNat: view natVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

elimStr ∷ (STACK) ⇒ ClearBaseVal → IM v 𝕊
elimStr cbv = error𝑂 (view strVL cbv) $
              throwIErrorCxt TypeIError "elimStr: view strVL cbv ≡ None" $ frhs
              [ ("cbv", pretty cbv)
              ]

----------------------------
--- PrinSetVal / PrinVal ---
----------------------------

elimPrinArr ∷ (STACK) ⇒ PrinSetVal → IM v (Prin ∧ ℕ)
elimPrinArr ρsv = error𝑂 (view arrPSVL ρsv) $
              throwIErrorCxt TypeIError "elimArr: view arrPSVL ρsv ≡ None" $ frhs
              [ ("ρsv", pretty ρsv)
              ]

elimPSV ∷ (STACK) ⇒ PrinSetVal → 𝑃 PrinVal
elimPSV = \case
  PowPSV ρ𝑃  → ρ𝑃
  ArrPSV ρ n → pow [ AccessPV ρ i | i ← [0..(n - 1)] ]

-----------------
--- Utilities ---
-----------------

metaBaseVal ∷ (STACK) ⇒ BaseVal e → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaBaseVal = \case
  Clear _cbv          → None
  Encrypted φ ρ𝑃 _ebv → Some $ φ :* ρ𝑃

metaMeet ∷ (STACK) ⇒ 𝑂 (Prot ∧ 𝑃 PrinVal) → 𝑂 (Prot ∧ 𝑃 PrinVal) → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaMeet meta₁ meta₂ = case (meta₁, meta₂) of
  (None      , None      ) → None
  (Some _φρ𝑃₁, None      ) → meta₁
  (None      , Some _φρ𝑃₂) → meta₂
  (Some _φρ𝑃₁, Some _φρ𝑃₂) → meta₁

metaBaseVals ∷ (STACK) ⇒ 𝐿 (BaseVal e) → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaBaseVals = foldFromWith None $ \ bv acc → metaMeet (metaBaseVal bv) acc

typeFrClearBaseVal ∷ ClearBaseVal → BaseType
typeFrClearBaseVal = \case
  BulV          → UnitT
  BoolV _b      → 𝔹T
  NatV pr _n    → ℕT pr
  IntV pr _i    → ℤT pr
  FltV pr _f    → 𝔽T pr
  StrV _s       → 𝕊T
  PrinV _ρv     → ℙT
  PrinSetV _ρsv → ℙsT

defaultClearBaseVal ∷ BaseType → ClearBaseVal
defaultClearBaseVal = \case
  UnitT → BulV
  𝔹T    → BoolV null
  ℕT pr → NatV pr null
  ℤT pr → IntV pr null
  𝔽T pr → FltV pr null
  𝕊T    → StrV null
  ℙT    → undefined -- TODO
  ℙsT   → undefined -- TODO
