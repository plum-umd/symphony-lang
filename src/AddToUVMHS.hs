module AddToUVMHS 
  ( module AddToUVMHS
  , module GHC.Stack
  ) where

import UVMHS

import GHC.Stack (CallStack,callStack,withFrozenCallStack)
import qualified GHC.Stack as HS

import System.Directory as HS

files ∷ IO (𝐿 𝕊)
files = list ∘ map string ^$ HS.listDirectory $ chars "."

indir ∷ 𝕊 → IO a → IO a
indir = HS.withCurrentDirectory ∘ chars

instance Pretty CallStack where pretty = ppString ∘ string ∘ HS.prettyCallStack

inFailT ∷ (Monad m) ⇒ m a → FailT m a
inFailT xM = FailT $ Some ^$ xM
