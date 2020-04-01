module AddToUVMHS 
  ( module AddToUVMHS
  , module UVMHS
  , module GHC.Stack
  ) where

import UVMHS

import GHC.Stack (CallStack,callStack,withFrozenCallStack)

import System.Directory as Directory

success ∷ (Monad m) ⇒ m a → FailT m a
success xM = FailT $ Some ^$ xM

-- instance DivMod 𝔻 where {(⌿) = (HS./);(÷) = HS.mod'}

touchDirs ∷ 𝕊 → IO ()
touchDirs = Directory.createDirectoryIfMissing True ∘ chars

iterS ∷ (ToIter a t,Sized t) ⇒ t → 𝐼S a
iterS xs = 𝐼S (size xs) $ iter xs
