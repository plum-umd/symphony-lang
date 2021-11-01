module Main where

import Prelude
import Data.String
import Test.Hspec

import qualified AddToUVMHSSpec as AddToUVMHS
import qualified SymphonySpec as Symphony

spec ∷ Spec
spec = do
  describe "ALL" $ do
    AddToUVMHS.spec
    Symphony.spec

main ∷ IO ()
main = hspec spec
