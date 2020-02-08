module AddToUVMHS 
  ( module AddToUVMHS
  , module GHC.Stack
  ) where

import UVMHS

import GHC.Stack (CallStack,callStack,withFrozenCallStack)
import qualified GHC.Stack as HS

import System.Directory as HS
import Data.Fixed as HS
import qualified Prelude as HS

files ∷ IO (𝐿 𝕊)
files = list ∘ map string ^$ HS.listDirectory $ chars "."

indir ∷ 𝕊 → IO a → IO a
indir = HS.withCurrentDirectory ∘ chars

instance Pretty CallStack where pretty = ppString ∘ string ∘ HS.prettyCallStack

success ∷ (Monad m) ⇒ m a → FailT m a
success xM = FailT $ Some ^$ xM

zipSameLength ∷ 𝐿 a → 𝐿 b → 𝑂 (𝐿 (a ∧ b))
zipSameLength xs ys = case (xs,ys) of
  (Nil,Nil) → return Nil
  (x:&xs',y:&ys') → do
    xys ← zipSameLength xs' ys'
    return $ (x:*y) :& xys
  _ → abort

unconsL ∷ 𝐿 a ⌲ (a ∧ 𝐿 a)
unconsL = Prism (curry (:&)) $ \case { x:&xs → Some (x:*xs) ; _ → None}

instance DivMod 𝔻 where {(⌿) = (HS./);(÷) = HS.mod'}
