module AddToUVMHS 
  ( module AddToUVMHS
  , module UVMHS
  , module GHC.Stack
  ) where

import UVMHS

import GHC.Stack (CallStack,callStack,withFrozenCallStack)
import qualified Data.Text.IO as Text

import System.Directory as Directory

import System.FilePath.Posix as FP

success ∷ (Monad m) ⇒ m a → FailT m a
success xM = FailT $ Some ^$ xM

-- instance DivMod 𝔻 where {(⌿) = (HS./);(÷) = HS.mod'}

writeAppend ∷ 𝕊 → 𝕊 → IO ()
writeAppend = Text.appendFile ∘ chars

pathFn ∷ 𝕊 → 𝕊
pathFn = string ∘ FP.takeFileName ∘ chars

pathBn ∷ 𝕊 → 𝕊
pathBn = string ∘ FP.takeBaseName ∘ chars

pathDir ∷ 𝕊 → 𝕊
pathDir = string ∘ FP.takeDirectory ∘ chars

pathExt ∷ 𝕊 → 𝕊
pathExt = string ∘ FP.takeExtension ∘ chars

rmDirs ∷ 𝕊 → IO ()
rmDirs = Directory.removeDirectoryRecursive ∘ chars
