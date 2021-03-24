module PSL.Interpreter.YaoN where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

instance Protocol 'YaoN_P where
  type ProtocolVal 'YaoN_P = Ckt
