module Symphony.TypeChecker.TLM.Operations where

import UVMHS

import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM.Types

runTLM ∷ TLR → TLS → TLM a → TLE ∨ (TLS ∧ TLW ∧ a)
runTLM r s = unID ∘ unErrorT ∘ runRWST r s ∘ unTLM

runTLMIO ∷ TLR → TLS → 𝕊 → TLM a → IO (TLS ∧ TLW ∧ a)
runTLMIO r s name c = case runTLM r s c of
    Inl e → do
      pprint $ ppHorizontal [ ppErr ">", ppBD $ ppString name ]
      printError e
      abortIO
    Inr a → return a

evalTLMIO ∷ TLR → TLS → 𝕊 → TLM a → IO a
evalTLMIO r s name = map snd ∘ runTLMIO r s name
