module AddToUVMHS 
  ( module AddToUVMHS
  , module UVMHS
  , module GHC.Stack
  ) where

import UVMHS

import GHC.Stack (CallStack,callStack,withFrozenCallStack)

-- import System.Directory as Directory

success ∷ (Monad m) ⇒ m a → FailT m a
success xM = FailT $ Some ^$ xM

-- instance DivMod 𝔻 where {(⌿) = (HS./);(÷) = HS.mod'}


