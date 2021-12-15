module Symphony.TypeChecker.EM.Operations where

import UVMHS

import Symphony.TypeChecker.EM.Types

runEM ∷ ER → ES → EM a → EE ∨ (ES ∧ EW ∧ a)
runEM r s = unID ∘ unErrorT ∘ runRWST r s ∘ unEM
