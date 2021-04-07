module PSL.Interpreter.Share where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Error

import PSL.Interpreter.Plain ()
import PSL.Interpreter.Yao ()
import PSL.Interpreter.YaoN ()

withProt ∷ (Monad m, MonadReader ICxt m, MonadError IError m, STACK) ⇒ Prot → (∀ (p ∷ Prot). (Protocol p) ⇒ P p → SProt p → m b) → m b
withProt φ k = case φ of
  PlainP → k P SPlainP
  YaoNP  → k P SYaoNP
  Yao2P  → k P SYao2P
--  BGWP   → k P SBGWP
--  GMWP   → k P SGMWP
--  BGVP   → k P SBGVP
--  SPDZP  → k P SSPDZP
--  AutoP  → k P SAutoP
  _      → throwIErrorCxt NotImplementedIError "withProt: φ" $ frhs [ ("φ", pretty φ) ]
