module Symphony.TypeChecker.EM.Operations where

import UVMHS

import Symphony.TypeChecker.Error
import Symphony.TypeChecker.EM.Types

runEM ∷ ER → ES → EM a → EE ∨ (ES ∧ EW ∧ a)
runEM r s = unID ∘ unErrorT ∘ runRWST r s ∘ unEM

evalEM ∷ ER → ES → EM a → EE ∨ a
evalEM r s c = mapInr (\ (_ :* _ :* a) → a) $ runEM r s c

evalEMIO ∷ ER → ES → 𝕊 → EM a → IO a
runTMIO cxt name xM = case runTM cxt xM of
  Inr x → return x
  Inl e → do
    pprint $ ppHorizontal [ ppErr ">", ppBD $ ppString name ]
    printError e
    abortIO

evalEMErr ∷ (Monad m, MonadError Error m, STACK) ⇒ ER → ES → EM a → m a
evalEMErr r s c = case evalEM r s c of
  Inl e → throw e
  Inr a → return a
