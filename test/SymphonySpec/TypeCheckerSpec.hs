module SymphonySpec.TypeCheckerSpec where

import Prelude
import Data.String
import Test.Hspec

import qualified UVMHS as UVM

import Symphony.Syntax
import Symphony.TypeChecker
import Symphony.TypeChecker.EM.Operations
import Symphony.TypeChecker.EM.Types
import Symphony.TypeChecker.Error


spec ∷ Spec
spec = do
  describe "synExp" $ do
    it "() : unit" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExp BulE))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.AddTop ThisPSE) (BaseT UnitT))
    it "() : bool" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExp (BoolE True)))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.AddTop ThisPSE) (BaseT 𝔹T))
    it "() : prinexp" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExp (PrinE (VarPE (UVM.var "A")))))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙT))

     