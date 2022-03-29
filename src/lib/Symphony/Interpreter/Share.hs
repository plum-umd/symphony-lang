module Symphony.Interpreter.Share where

import UVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.Dist.Types
import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.Error

withProt ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, STACK) ⇒ Prot → (∀ (p ∷ Prot). (Protocol p) ⇒ SProt p → m b) → m b
withProt φ k = case φ of
  PlainP    → todoCxt
  YaoNP     → todoCxt
  Yao2P     → todoCxt
  BGWP      → todoCxt
  GMWP      → todoCxt
  BGVP      → todoCxt
  SPDZP     → todoCxt
  AutoP     → todoCxt
