module Symphony.Dynamic.Seq.Lens where

import UVMHS

import Symphony.Lang.Syntax
import Symphony.Dynamic.Seq.Types

import qualified Prelude as HS

----------------------------
--- PrinSetVal / PrinVal ---
----------------------------

makePrisms ''PrinSetVal
makePrisms ''PrinVal

-------------
--- TYPES ---
-------------

baseTL ∷ Type ⌲ BaseType
baseTL = prism constr destr
  where constr bτ = BaseT bτ
        destr = \case
          BaseT bτ → Some bτ
          _        → None

pairTL ∷ Type ⌲ Type ∧ Type
pairTL = prism constr destr
  where constr (τ₁ :* τ₂) = τ₁ :×: τ₂
        destr = \case
          τ₁ :×: τ₂ → Some $ τ₁ :* τ₂
          _ → None

sumTL ∷ Type ⌲ Type ∧ Type
sumTL = prism constr destr
  where constr (τ₁ :* τ₂) = τ₁ :+: τ₂
        destr = \case
          τ₁ :+: τ₂ → Some $ τ₁ :* τ₂
          _ → None

listTL ∷ Type ⌲ (ℕ ∧ Type)
listTL = prism constr destr
  where constr (n :* τ) = ListT n τ
        destr = \case
          ListT n τ → Some (n :* τ)
          _ → None

arrTL ∷ Type ⌲ (ℕ ∧ Type)
arrTL = prism constr destr
  where constr (n :* τ) = ArrT n τ
        destr = \case
          ArrT n τ → Some (n :* τ)
          _ → None

-----------
-- STATE --
-----------

makeLenses ''IState

--------------------
-- TOPLEVEL STATE --
--------------------

makeLenses ''ITLState
