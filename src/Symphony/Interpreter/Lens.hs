module Symphony.Interpreter.Lens where

import UVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types

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

arrTL ∷ Type ⌲ (𝑂 EMode ∧ ℕ ∧ Type)
arrTL = prism constr destr
  where constr (em :* n :* τ) = ArrT em n τ
        destr = \case
          ArrT em n τ → Some (em :* n :* τ)
          _ → None

--------------
-- Circuits --
--------------

makeLenses ''Ckt
makePrisms ''Input
makePrisms ''Gate

-----------
-- STATE --
-----------

makeLenses ''IState

iStateShareInfoNextWireL ∷ (((𝑃 PrinVal) ⇰ Wire) ∧ 𝑃 PrinVal) ⟢ Wire
iStateShareInfoNextWireL = lens getCkt setCkt
  where getCkt (ws :* ρvs)   = case lookup𝐷 ws ρvs of
                             None   → HS.fromIntegral 0
                             Some w → w
        setCkt (ws :* ρvs) w = (ρvs ↦ w) ⩌ ws :* ρvs

iStateShareInfoNextWiresL ∷ 𝑃 PrinVal → IState v ⟢ (((𝑃 PrinVal) ⇰ Wire) ∧ 𝑃 PrinVal)
iStateShareInfoNextWiresL ρvs = lens getCkts setCkts
  where getCkts st = access iStateNextWiresL st :* ρvs
        setCkts st (ws :* _ρvs) = update iStateNextWiresL ws st

iStateNextWireL ∷ 𝑃 PrinVal → IState v ⟢ Wire
iStateNextWireL m = iStateShareInfoNextWireL ⊚ (iStateShareInfoNextWiresL m)

------------
-- OUTPUT --
------------

makeLenses ''ResEv

--------------------
-- TOPLEVEL STATE --
--------------------

makeLenses ''ITLState
