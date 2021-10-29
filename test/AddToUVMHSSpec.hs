module AddToUVMHSSpec where

import Prelude
import Data.String
import Test.Hspec

import qualified UVMHS as UVM
import AddToUVMHS

spec ∷ Spec
spec = do
  describe "fromSome" $ do
    it "..." $ do
      fromSome (UVM.Some 10) `shouldBe` 10
