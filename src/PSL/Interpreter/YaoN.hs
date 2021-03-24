module PSL.Interpreter.YaoN where

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

instance Protocol 'YaoNP where
  type ProtocolVal 'YaoNP = Ckt
