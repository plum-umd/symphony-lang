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
      x ← runTMIO UVM.null "" (synExp BulE)
      x `shouldBe` BaseT UnitT
    it "True : bool" $ do
      x ← runTMIO UVM.null "" (synExp (BoolE True))
      x `shouldBe` BaseT 𝔹T
