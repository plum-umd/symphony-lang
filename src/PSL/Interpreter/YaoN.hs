module PSL.Interpreter.YaoN where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

instance Protocol 'YaoN_P where
  type ProtocolVal 'YaoN_P = Ckt

  typeOf ∷ P 'YaoN_P → Ckt → IM Type
  typeOf = undefined

  defaultOf ∷ P 'YaoN_P → Type → IM Ckt
  defaultOf = undefined

  exePrim ∷ P 'YaoN_P → Op → 𝐿 Ckt → IM Ckt
  exePrim = undefined
