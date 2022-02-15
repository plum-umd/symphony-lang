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

 
 
    it "() : primexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t' = (SecT UVM.Top (BaseT 𝔹T ))
          t = (SecT UVM.Top (BaseT 𝔹T ))
          t'' = (SecT UVM.Top (BaseT 𝔹T ))
          lexpr = (UVM.frhs [(UVM.𝐴 y (VarE (UVM.var "A"))), (UVM.𝐴 y (VarE (UVM.var "B")))])
          expr =  (PrimE AndO lexpr )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr d -> d `shouldBe`  t''

    it "() : prodexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t' = (SecT UVM.Top (BaseT 𝔹T ))
          t = (SecT UVM.Top (BaseT 𝔹T ))
          expr =  (ProdE  (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr d -> d `shouldBe`  (SecT UVM.Top (t :×: t'))
    it "() : annotatedbul" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT (UVM.Top) (BaseT UnitT))
          expr =  (AscrE  (nullExp (BulE)) t )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedbul2" $ 
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
          expr =  (AscrE  (nullExp (LE (nullExp (BulE)))) t )
          t = (SecT  (UVM.Top) ((SecT (UVM.Top) (BaseT UnitT)) :+: (SecT (UVM.Top) (BaseT 𝔹T)))) 
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedright" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          expr =  (AscrE  (nullExp (RE (nullExp (BulE)))) t )
          t =  (SecT  (UVM.Top)  ((SecT (UVM.Top) (BaseT 𝔹T )) :+: (SecT (UVM.Top) (BaseT UnitT))))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatednil" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t' = (SecT (UVM.Top) (BaseT UnitT))
          t = (SecT (UVM.Top) (ListT 1 t')) 
          expr =  (AscrE  (nullExp (NilE)) t )
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : cons" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t' = (SecT (UVM.Top) (BaseT UnitT))
          t = (SecT (UVM.Top) (ListT 1 t')) 
          expr2 =  (AscrE  (nullExp (NilE)) t )
          expr1 =  BulE
          expr =  (ConsE (nullExp expr1) (nullExp expr2))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t

    it "() : let" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT (UVM.Top) (BaseT UnitT))
          expr2 =  (VarE (UVM.var "x"))
          expr1 =  BulE
          expr =  (LetE (VarP (UVM.var "x")) (nullExp expr1) (nullExp expr2))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t

    it "() : let2" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT (UVM.Top) (BaseT 𝔹T))
          expr2 =  (BoolE True)
          expr1 =  BulE
          expr =  (LetE (BulP) (nullExp expr1) (nullExp expr2))
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : caseexp" $  
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          exprL = ( (LP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "A"))) )
          exprR = ((RP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "B"))))
          expr =  (CaseE (nullExp (VarE (UVM.var "D"))) (UVM.frhs [exprL, exprR] ) )
          guardt = (SecT UVM.Top ((SecT a (BaseT UnitT )) :+: (SecT a (BaseT UnitT ))))  
          x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , guardt), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))
    it "() : readbul" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (ReadE  t (nullExp (StrE "Test")) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = m, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
      in case x of
        UVM.Inr a -> a `shouldBe`  t
       it "() : readbulbad" $ 
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) )) 
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )) 
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) 
          t = (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (ReadE  t (nullExp BUlE) )
          x  = (evalEM (ER {terSource = UVM.None, terMode = m, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr)) 
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