module Symphony.Dynamic.Par.Share where

import UVMHS

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Dist.Types
import Symphony.Dynamic.Par.Error

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
