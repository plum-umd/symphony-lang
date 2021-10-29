module Allyn.Interpreter.Share where

import UVMHS

import Allyn.Syntax
import Allyn.Interpreter.Types
import Allyn.Interpreter.Dist.Types
import Allyn.Interpreter.Pretty ()
import Allyn.Interpreter.Error

import Allyn.Interpreter.Plain ()
import Allyn.Interpreter.Yao ()

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
  GMWP      → todoCxt
  BGVP      → todoCxt
  SPDZP     → todoCxt
  AutoP     → todoCxt
