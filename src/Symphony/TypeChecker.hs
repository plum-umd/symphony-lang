module Symphony.TypeChecker where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.TLM
import Symphony.TypeChecker.EM

---------------
-- Utilities --
---------------

asTLE ∷ EE → TLE
asTLE e = undefined

asTLM ∷ EM a → TLM a
asTLM eM = do
  γ ← getL ttlsEnvL
  let θ = ER { terEnv = γ }
  let r = runEM θ () eM
  case r of
    Inl ee            → throw $ asTLE ee
    Inr (_ :* _ :* a) → return a

------------------
-- TypeChecking --
------------------

synProg ∷ 𝐿 TL → TLM Type
synProg prog = do
  eachOn prog bindTL
  asTLM $ do
    τMain ← synVar $ var "main"
    synApp τMain $ BaseT UnitT

bindTL ∷ TL → TLM ()
bindTL tl = todoError

synVar ∷ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → return τ
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]

synApp ∷ Type → Type → EM Type
synApp = undefined
