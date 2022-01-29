module Symphony.Interpreter.Share where

import UVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.Dist.Types
import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.Error

import Symphony.Interpreter.Plain ()
import Symphony.Interpreter.Yao ()
import Symphony.Interpreter.GMW ()

proxySProt ∷ SProt p → P p
proxySProt = \case
  SPlainP    → P
  SYaoPlainP → P
  SYaoNP     → P
  SYao2P     → P
  SBGWP      → P
  SGMWP      → P
  SBGVP      → P
  SSPDZP     → P
  SAutoP     → P

withProt ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, STACK) ⇒ Prot → (∀ (p ∷ Prot). (Protocol p) ⇒ P p → SProt p → m b) → m b
withProt φ k = case φ of
  PlainP    → k P SPlainP
  YaoPlainP → k P SYaoPlainP
  YaoNP     → todoCxt
  Yao2P     → k P SYao2P
  BGWP      → todoCxt
  GMWP      → k P SGMWP
  BGVP      → todoCxt
  SPDZP     → todoCxt
  AutoP     → todoCxt
