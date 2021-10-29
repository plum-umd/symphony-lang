module Allyn.Interpreter.Plain where

import UVMHS

import Allyn.Syntax
import Allyn.Interpreter.Types
import Allyn.Interpreter.Dist.Types
import Allyn.Interpreter.BaseVal
import Allyn.Interpreter.Error
import Allyn.Interpreter.Primitives
import Allyn.Interpreter.Pretty ()
import Allyn.Interpreter.Lens ()

instance Protocol 'PlainP where
  type Share 'PlainP = ClearBaseVal

  share ∷ P 'PlainP → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → IM DistVal ClearBaseVal
  share _p _ρvFr _ρvsTo = \case
    Inl bvc → return bvc
    Inr _bτ → impossibleCxt

  embed ∷ P 'PlainP → 𝑃 PrinVal → ClearBaseVal → IM DistVal ClearBaseVal
  embed _p _ρvsFrTo = return

  prim ∷ P 'PlainP → 𝑃 PrinVal → Op → 𝐿 ClearBaseVal → IM DistVal ClearBaseVal
  prim _p _ρvsC = evalPrimClearBaseVal

  reveal ∷ P 'PlainP → 𝑃 PrinVal → PrinVal → ClearBaseVal → IM DistVal ClearBaseVal
  reveal _p _ρvsFr _ρvTo bv = return bv
