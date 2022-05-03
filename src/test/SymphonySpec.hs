module SymphonySpec where

import Prelude
import Data.String
import Test.Hspec

import SymphonySpec.TypeCheckerSpec as TypeChecker

spec ∷ Spec
spec = do
  describe "SymphonySpec" $ do
    TypeChecker.spec
