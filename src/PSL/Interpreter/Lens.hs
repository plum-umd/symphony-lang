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
makePrisms ''ValP
makePrisms ''UnShare
makePrisms ''MPCVal

--------------
-- Circuits --
--------------

makeLenses ''Ckt
makePrisms ''Input
makePrisms ''Gate
makePrisms ''BaseGate

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

iStateShareInfoNextWireL ∷ ((Mode ⇰ Wire) ∧ Mode) ⟢ Wire
iStateShareInfoNextWireL = lens getCkt setCkt
  where getCkt (ws :* m)   = case lookup𝐷 ws m of
                             None   → HS.fromIntegral 0
                             Some w → w
        setCkt (ws :* m) w = (m ↦ w) ⩌ ws :* m

iStateShareInfoNextWiresL ∷ Mode → IState ⟢ ((Mode ⇰ Wire) ∧ Mode)
iStateShareInfoNextWiresL m = lens getCkts setCkts
  where getCkts st = access iStateNextWiresL st :* m
        setCkts st (ws :* _m) = update iStateNextWiresL ws st

iStateNextWireL ∷ Mode → IState ⟢ Wire
iStateNextWireL m = iStateShareInfoNextWireL ⊚ (iStateShareInfoNextWiresL m)

------------
-- OUTPUT --
------------

makeLenses ''ResEv

--------------------
-- TOPLEVEL STATE --
--------------------

makeLenses ''ITLState
