module Command.Tc where

import Symphony.Prelude

import Symphony.Lang.Parser

import Symphony.TypeChecker
import Symphony.TypeChecker.TLM

runTc ∷ 𝐿 𝕊 → IO Doc
runTc args = do
  program ← io $ map concat $ mapM parseFile args
  τ       ← io $ evalTLMIO tlr₀ tls₀ "" $ synProg program
  return $ pretty τ
