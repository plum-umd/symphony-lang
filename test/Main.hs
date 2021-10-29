module Main where

import Prelude
import Data.String
import Test.Hspec

import qualified AddToUVMHSSpec as AddToUVMHS
import qualified AllynSpec as Allyn

spec ∷ Spec
spec = do
  describe "ALL" $ do
    AddToUVMHS.spec
    Allyn.spec

main ∷ IO ()
main = hspec spec
