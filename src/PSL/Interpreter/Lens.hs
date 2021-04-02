module PSL.Interpreter.Lens where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types

import qualified Prelude as HS

------------
-- VALUES --
------------

makePrisms ''Val
makePrisms ''BaseVal

sSecVPL ∷ ValP ⌲ Mode ∧ Val
sSecVPL = prism constr destr
  where constr (m :* v) = SSecVP m v
        destr = \case
          SSecVP m v → Some $ m :* v
          _ → None

iSecVPL ∷ ValP ⌲ PrinVal ⇰ Val
iSecVPL = prism constr destr
  where constr b = ISecVP b
        destr = \case
          ISecVP b → Some b
          _ → None

--makePrisms ''ValP
--makePrisms ''UnShare

baseMVL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ MPCVal p ⌲ (ProtocolVal p)
baseMVL = prism constr destr
  where constr pv = BaseMV pv
        destr = \case
          BaseMV pv → Some pv
          _         → abort

--------------
-- Circuits --
--------------

makeLenses ''Ckt
makePrisms ''Input
makePrisms ''Gate

------------
-- PARAMS --
------------

makeLenses ''IParams

-------------
-- CONTEXT --
-------------

makeLenses ''ICxt

iCxtIsExampleL ∷ ICxt ⟢ 𝔹
iCxtIsExampleL = iParamsIsExampleL ⊚ iCxtParamsL

iCxtLocalModeL ∷ ICxt ⟢ Mode
iCxtLocalModeL = iParamsLocalModeL ⊚ iCxtParamsL

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

iStateShareInfoNextWiresL ∷ 𝑃 PrinVal → IState ⟢ (((𝑃 PrinVal) ⇰ Wire) ∧ 𝑃 PrinVal)
iStateShareInfoNextWiresL ρvs = lens getCkts setCkts
  where getCkts st = access iStateNextWiresL st :* ρvs
        setCkts st (ws :* _ρvs) = update iStateNextWiresL ws st

iStateNextWireL ∷ 𝑃 PrinVal → IState ⟢ Wire
iStateNextWireL m = iStateShareInfoNextWireL ⊚ (iStateShareInfoNextWiresL m)

------------
-- OUTPUT --
------------

makeLenses ''ResEv

--------------------
-- TOPLEVEL STATE --
--------------------

makeLenses ''ITLState
