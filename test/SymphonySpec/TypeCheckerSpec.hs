module SymphonySpec.TypeCheckerSpec where

import Prelude
import Data.String
import Test.Hspec

import qualified UVMHS as UVM

import Symphony.Syntax
import Symphony.TypeChecker
import Symphony.TypeChecker.Types

spec ∷ Spec
spec = do
  describe "synExp" $ do
    it "() : unit" $ do
      x ← return $ runTMIO UVM.null "" (synExp BulE)
      case x of
      Inr x →  x `shouldBe` BaseT UnitT
      Inl x →  x `shouldBe` BaseT UnitT
     

