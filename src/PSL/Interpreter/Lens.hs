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
--makePrisms ''ValP
makeLenses ''MPCify
--makePrisms ''UnShare
--makePrisms ''MPCVal

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
