module Symphony.Interpreter.GMW where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Dist.Types
import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.Error

instance Protocol 'GMWP where
  type Share 'GMWP = Semi64Val

  share ∷ P 'GMWP → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → IM DistVal Semi64Val
  share _p = gmwShare

  embed ∷ P 'GMWP → 𝑃 PrinVal → ClearBaseVal → IM DistVal Semi64Val
  embed _p = gmwEmbed

  prim ∷ P 'GMWP → 𝑃 PrinVal → Op → 𝐿 Semi64Val → IM DistVal Semi64Val
  prim _p = gmwPrim

  reveal ∷ P 'GMWP → 𝑃 PrinVal → PrinVal → Semi64Val → IM DistVal ClearBaseVal
  reveal _p = gmwReveal

gmwShare ∷ PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → IM DistVal Semi64Val
gmwShare ρvFr ρvsTo cbvorbτ = do
  gmwCheckShare ρvFr ρvsTo
  s64p ← getOrMkSession ρvsTo
  let bvc = elimChoice id defaultClearBaseVal cbvorbτ
  semi64Share s64p bvc

gmwCheckShare ∷ PrinVal → 𝑃 PrinVal → IM DistVal ()
gmwCheckShare ρvFr ρvsTo = do
  guardErr (ρvFr ∈ ρvsTo) $
    throwIErrorCxt TypeIError "gmwCheckShare: ρvFr ∉ ρvsTo" $ frhs
    [ ("ρvFr", pretty ρvFr)
    , ("ρvsTo", pretty ρvsTo)
    ]

semi64Share ∷ Semi64Protocol → ClearBaseVal → IM DistVal Semi64Val
semi64Share s64p cbv = return ()

gmwEmbed ∷ 𝑃 PrinVal → ClearBaseVal → IM DistVal Semi64Val
gmwEmbed ρvsFrTo cbv = return ()

gmwPrim ∷ 𝑃 PrinVal → Op → 𝐿 Semi64Val → IM DistVal Semi64Val
gmwPrim ρvsC op gvs = return ()

gmwReveal ∷ 𝑃 PrinVal → PrinVal → Semi64Val → IM DistVal ClearBaseVal
gmwReveal ρvsFr ρvTo gv = return BulV

getOrMkSession ∷ 𝑃 PrinVal → IM DistVal Semi64Protocol
getOrMkSession ρvsC = return ()
