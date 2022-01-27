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
    it "() : unit" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExpR BulE))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.Top) (BaseT UnitT))
    it "() : unit2" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExp (UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (BulE))))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.Top) (BaseT UnitT))
    it "() : unit3" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ]))) , terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙsT))) ])) }) () (synExpR BulE))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT UnitT))
    it "() : bool" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExpR (BoolE True)))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top (BaseT 𝔹T))
    it "() : prinexp" $ let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinE (VarPE (UVM.var "A")))))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙT))

    it "() : prinset2exp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
    it "() : prinset2exp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT)) 
    it "() : ifexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (IfE (UVM.𝐴 y (VarE (UVM.var "D"))) (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))
    it "() : ifexp2" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (IfE (UVM.𝐴 y (VarE (UVM.var "D"))) (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ]))) , terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT a (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))  
    it "() : varexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          exp =  (UVM.𝐴 y (VarE (UVM.var "A")))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExp exp)) 
      in case x of
      UVM.Inr d -> d `shouldBe`  (SecT a  (BaseT UnitT))
    it "() : prodexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (ProdE  (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr d -> d `shouldBe`  (SecT UVM.Top ((SecT a  (BaseT UnitT)) :×: (SecT b  (BaseT UnitT))))
    it "() : annotatednil" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT (UVM.Top) (BaseT UnitT))
          expr =  (AscrE  (nullExp (BulE)) t )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatednil2" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT UnitT))
          expr =  (AscrE  (nullExp (BulE)) t )
          x  =  (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = UVM.null}) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedleft" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (AscrE  (LE (nullExp (BulE))) t )
          t = (SecT (UVM.Top) (BaseT UnitT)) :+: (SecT (UVM.Top) (BaseT 𝔹T))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedright" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (AscrE  (RE (nullExp (BulE))) t )
          t = (SecT (UVM.Top) (BaseT 𝔹T )) :+: (SecT (UVM.Top) (BaseT UnitT))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
   
   {- it "() : nilexp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
     AscrE-}
  --  it "() : prinset3exp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙsT))) ])) }) () (synExp (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
  --   in  case x of
   --  UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
   --(UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (BulE))
   -- (UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (VarE (UVM.var "A")))