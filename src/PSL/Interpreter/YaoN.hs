module PSL.Interpreter.YaoN where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types

instance Protocol 'YaoN_P where
  type ProtocolVal 'YaoN_P = Ckt
  exePrim ∷ P 'YaoN_P → Op → 𝐿 Ckt → IO Ckt
  exePrim = undefined
