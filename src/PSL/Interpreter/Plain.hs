module PSL.Interpreter.Plain where

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

instance Protocol 'Plain where
  type ProtocolVal 'Plain = Val
