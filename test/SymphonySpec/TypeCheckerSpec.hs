module SymphonySpec.TypeCheckerSpec where

import Prelude
import Data.Text as Text
import Data.String
import Test.Hspec

import qualified UVMHS as UVM

import Symphony.Syntax
import Symphony.TypeChecker
import Symphony.TypeChecker.EM.Operations
import Symphony.TypeChecker.EM.Types
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.Operations


spec ∷ Spec
spec = do
  describe "synExp" $ do
    it "() : unit" $ let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = UVM.null}) () (synExpR BulE))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.Top) (BaseT UnitT))
    it "() : unit2" $ let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = UVM.null}) () (synExp (UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (BulE))))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.Top) (BaseT UnitT))
    it "() : unit3" $ let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))) , terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙsT))) ])) }) () (synExpR BulE))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT UnitT))
    it "() : bool" $ let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = UVM.null}) () (synExpR (BoolE True)))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top (BaseT 𝔹T))
    it "() : prinexp" $ let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinE (VarPE (UVM.var "A")))))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙT))

    it "() : prinset2exp" $  let x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
   -- it "() : prinset2exp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
  --   in  case x of
 --    UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
    it "() : ifexp" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          expr =  (IfE (UVM.𝐴 y (VarE (UVM.var "D"))) (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))
    it "() : ifexp2" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          expr =  (IfE (UVM.𝐴 y (VarE (UVM.var "D"))) (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))) , terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT a (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))
    it "() : varexp" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          exp =  (UVM.𝐴 y (VarE (UVM.var "A")))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExp exp))
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
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr d -> d `shouldBe`  t''


    it "() : primexp2" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT UVM.Top (BaseT 𝔹T ))
          t = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT 𝔹T) ))
          t'' = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT 𝔹T) ))
          lexpr = (UVM.frhs [(UVM.𝐴 y (VarE (UVM.var "A"))), (UVM.𝐴 y (VarE (UVM.var "B")))])
          expr =  (PrimE AndO lexpr )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top)p, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr d -> d `shouldBe`  t''
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e

    it "() : varexp2" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT UVM.Top (BaseT 𝔹T ))
          t = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT 𝔹T) ))
          t'' = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT 𝔹T) ))
          lexpr = (UVM.frhs [(UVM.𝐴 y (VarE (UVM.var "A"))), (UVM.𝐴 y (VarE (UVM.var "B")))])
          expr =  (VarE (UVM.var "B"))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr d -> d `shouldBe`  t'
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e

    it "() : prodexp" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT UVM.Top (BaseT 𝔹T ))
          t = (SecT UVM.Top (BaseT 𝔹T ))
          expr =  (ProdE  (UVM.𝐴 y (VarE (UVM.var "A"))) (UVM.𝐴 y (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , t'), (UVM.var "A" , t), (UVM.var "B" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr d -> d `shouldBe`  (SecT UVM.Top (t :×: t'))
    it "() : annotatedbul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT (UVM.Top) (BaseT UnitT))
          expr =  (AscrE  (nullExp (BulE)) t )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedbul2" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) )) (BaseT UnitT))
          expr =  (AscrE  (nullExp (BulE)) t )
          x  =  (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = UVM.null}) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedleft" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          expr =  (AscrE  (nullExp (LE (nullExp (BulE)))) t )
          t = (SecT  (UVM.Top) ((SecT (UVM.Top) (BaseT UnitT)) :+: (SecT (UVM.Top) (BaseT 𝔹T))))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatedright" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          expr =  (AscrE  (nullExp (RE (nullExp (BulE)))) t )
          t =  (SecT  (UVM.Top)  ((SecT (UVM.Top) (BaseT 𝔹T )) :+: (SecT (UVM.Top) (BaseT UnitT))))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatednil" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT (UVM.Top) (BaseT UnitT))
          t = (SecT (UVM.Top) (ListT 1 t'))
          expr =  (AscrE  (nullExp (NilE)) t )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
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
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
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
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
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
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
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
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , guardt), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  (SecT c  (BaseT UnitT))
    it "() : readbul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT c (BaseT UnitT))
          t' = (BaseT UnitT)
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (ReadE  t' (nullExp (StrE "Test")) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : writebul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (WriteE  (nullExp (BulE)) (nullExp (StrE "Test")) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : writebul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (WriteE  (nullExp (BulE)) (nullExp (StrE "Test")) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : annotatednillam" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT (UVM.Top) (BaseT UnitT))
          τ₁₁ =(SecT (UVM.Top) (BaseT UnitT))
          τ₁₂ =(SecT (UVM.Top) (BaseT UnitT))
          η =  Effect {effectInput = UVM.null, effectReveal = UVM.null,  effectMode = UVM.Top}
          t = SecT UVM.Top (τ₁₁ :→: (η UVM.:* τ₁₂)) 
          f = UVM.var "f"
          xvar = (UVM.var "x")
          lst = (UVM.frhs [(VarP xvar)] )
          expr =  (AscrE  (nullExp (LamE (UVM.Some f) lst (nullExp (VarE xvar)))) t )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : annotatednillam2" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
         
          τ₁₁ =(SecT (UVM.Top) (BaseT UnitT))
          τ₁₂ =(SecT (UVM.Top) (BaseT UnitT))
          η =  Effect {effectInput = UVM.null, effectReveal = UVM.null,  effectMode = UVM.Top}
          t' = SecT UVM.Top (τ₁₁ :→: (η UVM.:* τ₁₂)) 
          t = SecT UVM.Top (τ₁₁ :→: (η UVM.:* t')) 
          f = UVM.var "f"
          xvar = (UVM.var "x")
          yvar = (UVM.var "y")
          lst = (UVM.frhs [(VarP xvar), (VarP yvar)] )
          expr =  (AscrE  (nullExp (LamE (UVM.Some f) lst (nullExp (VarE xvar)))) t )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : app" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT (UVM.Top) (BaseT UnitT))
          τ₁₁ =(SecT (UVM.Top) (BaseT UnitT))
          τ₁₂ =(SecT (UVM.Top) (BaseT UnitT))
          η =  Effect {effectInput = UVM.null, effectReveal = UVM.null,  effectMode = UVM.Top}
          t = SecT UVM.Top (τ₁₁ :→: (η UVM.:* τ₁₂)) 
          f = UVM.var "f"
          xvar = (UVM.var "x")
          lst = (UVM.frhs [(VarP xvar)] )
          lamexpr =  (AscrE  (nullExp (LamE (UVM.Some f) lst (nullExp (VarE xvar)))) t )
          expr = (AppE (nullExp lamexpr) (nullExp BulE))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
        in case x of
        UVM.Inr a -> a `shouldBe`  t'
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : refbul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT c (RefT (UVM.Some c) (SecT c (BaseT UnitT))))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (RefE  (nullExp (BulE)) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : refreadbul" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t'= (SecT c (RefT (UVM.Some c) (SecT c (BaseT UnitT))))
          t = (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr' =  (RefE  (nullExp (BulE)) )
          expr = (RefReadE (nullExp expr'))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
    it "() : refwritenat" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t' = (SecT c (RefT (UVM.Some c) (SecT c (BaseT 𝔹T))))
          t = (SecT c (BaseT 𝔹T))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr' =  (RefE  (nullExp (BoolE True)) )
          expr = (RefWriteE (nullExp expr') (nullExp (BoolE False)))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : arr" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t = (SecT c (ArrT (UVM.Some c)  0 (SecT c (BaseT UnitT))))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr =  (ArrayE  (nullExp (NatE InfIPr 2))  (nullExp (BulE)) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : arrread" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t =  (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr' =  (ArrayE  (nullExp (NatE InfIPr 2))  (nullExp (BulE)) )
          expr = (ArrayReadE (nullExp expr') (nullExp (NatE InfIPr 2)) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : arrwrite" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t =  (SecT c (BaseT (UnitT)))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr'' =  (ArrayE  (nullExp (NatE InfIPr 2))  (nullExp (BulE)) )
          expr' = (ArrayReadE (nullExp expr'') (nullExp (NatE InfIPr 2)) )
          expr = (ArrayWriteE (nullExp expr') (nullExp (BulE)) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : arrrsize" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t =  (SecT c (BaseT (ℕT InfIPr)))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A") ])))
          expr' =  (ArrayE  (nullExp (NatE InfIPr 2))  (nullExp (BulE)) )
          expr = (ArraySizeE (nullExp expr')  )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : par" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          cpse = PowPSE (UVM.frhs [VarPE (UVM.var "A")])
          c = (UVM.AddTop (cpse))
          t =  (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr' =  (BulE)
          expr = (ParE cpse (nullExp expr')  )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e

    it "() : parempty" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          cpse = PowPSE (UVM.frhs [])
          c = (UVM.AddTop (cpse))
          t =  (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr' =  (NatE InfIPr 2)
          expr = (ParE cpse (nullExp expr')  )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : share" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          dpse = (PowPSE (UVM.frhs [ VarPE (UVM.var "C")]) )
          d = (UVM.AddTop (dpse))
          t' =  (BaseT UnitT)
          t =  (SecT d (ShareT YaoNP d (BaseT UnitT)) )
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr'' =  (BulE)
          expr' = (ParE cpse (nullExp expr'')  )
          expr = (ShareE YaoNP t'  aprin dpse (nullExp expr'))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : reveal" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          dpse = (PowPSE (UVM.frhs [ VarPE (UVM.var "C")]) )
          d = (UVM.AddTop (dpse))
          t =  (SecT c (BaseT UnitT))
          t' =  (BaseT UnitT)
          t'' =  (BaseT UnitT)
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr''' =  (BulE)
          expr'' = (ParE cpse (nullExp expr''')  )
          expr' = (ShareE YaoNP t''  aprin dpse (nullExp expr''))
          expr = (RevealE YaoNP t' dpse aprin (nullExp expr'))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : comm" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          dpse = (PowPSE (UVM.frhs [ VarPE (UVM.var "C")]) )
          d = (UVM.AddTop (dpse))
          t' =   (BaseT UnitT)
          t =  (SecT d  (BaseT UnitT)) 
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr'' =  (BulE)
          expr' = (ParE cpse (nullExp expr'')  )
          expr = (SendE t'  aprin dpse (nullExp expr'))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : muxifexp" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          dpse = (PowPSE (UVM.frhs [ VarPE (UVM.var "C")]) )
          d = (UVM.AddTop (dpse))
          t =  (SecT d (ShareT YaoNP d (BaseT UnitT)) )
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [  (SinglePV "C")])))
          expr =  (MuxIfE (nullExp (VarE (UVM.var "D"))) (nullExp (VarE (UVM.var "A"))) (nullExp (VarE (UVM.var "B"))) )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT d (ShareT YaoNP d (BaseT 𝔹T)) )), (UVM.var "A" , (SecT d (ShareT YaoNP d (BaseT UnitT)) )), (UVM.var "B" , (SecT d (ShareT YaoNP d (BaseT UnitT)) )) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : caseexp" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          exprL = ( (LP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "A"))) )
          exprR = ((RP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "B"))))
          expr =  (MuxCaseE (nullExp (VarE (UVM.var "D"))) (UVM.frhs [exprL, exprR] ) )
          t = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT UnitT)) )
          guardt = (SecT UVM.Top (ShareT YaoNP  UVM.Top ((SecT a (BaseT UnitT )) :+: (SecT a (BaseT UnitT )))))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , guardt), (UVM.var "A" , (SecT UVM.Top (BaseT UnitT ))), (UVM.var "B" , (SecT UVM.Top (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : caseexp" $
      let y = (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null})
          a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          exprL = ( (LP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "A"))) )
          exprR = ((RP (VarP (UVM.var "X"))) UVM.:*  (nullExp (VarE (UVM.var "B"))))
          expr =  (MuxCaseE (nullExp (VarE (UVM.var "D"))) (UVM.frhs [exprL, exprR] ) )
          t = (SecT UVM.Top (ShareT YaoNP UVM.Top (BaseT UnitT)) )
          guardt = (SecT UVM.Top (ShareT YaoNP  UVM.Top ((SecT a (BaseT UnitT )) :+: (SecT a (BaseT UnitT )))))
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , guardt), (UVM.var "A" ,  (SecT UVM.Top (ShareT YaoNP  UVM.Top  (BaseT UnitT )))), (UVM.var "B" ,  (SecT UVM.Top (ShareT YaoNP  UVM.Top  (BaseT UnitT )))) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : bundleexp" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          cprin = VarPE (UVM.var "C")
          dpse = (PowPSE (UVM.frhs [cprin]) )
          d = (UVM.AddTop (dpse))
          t' = (SecT c (BaseT UnitT)) 
          t'' = (SecT d (BaseT UnitT)) 
          t =  (SecT b (ISecT b (BaseT UnitT)) )
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          exprL = (aprin UVM.:*  (nullExp (VarE (UVM.var "x"))) )
          exprR = (cprin UVM.:*  (nullExp (VarE (UVM.var "y"))) )
          l =  (UVM.frhs [exprL, exprR] )
          expr =  (BundleE l)
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , t'),  (UVM.var "y" , t'' ) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : bundlereadexp" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          cprin = VarPE (UVM.var "C")
          dpse = (PowPSE (UVM.frhs [cprin]) )
          d = (UVM.AddTop (dpse))
          t' = (SecT c (BaseT UnitT)) 
          t'' = (SecT d (BaseT UnitT)) 
          t =  t'
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          exprL = (aprin UVM.:*  (nullExp (VarE (UVM.var "x"))) )
          exprR = (cprin UVM.:*  (nullExp (VarE (UVM.var "y"))) )
          l =  (UVM.frhs [exprL, exprR] )
          expr' =  (BundleE l)
          expr = (BundleAccessE (nullExp expr') aprin )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "x" , t'),  (UVM.var "y" , t'' ), (UVM.var "A" , (SecT UVM.Top (BaseT ℙT)))  ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : bundleunionexp" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          aprin = VarPE (UVM.var "A")
          cpse = PowPSE (UVM.frhs [aprin])
          c = (UVM.AddTop (cpse))
          cprin = VarPE (UVM.var "C")
          dpse = (PowPSE (UVM.frhs [cprin]) )
          d = (UVM.AddTop (dpse))
          t' = (SecT b (ISecT c (BaseT UnitT)) ) 
          t'' = (SecT b (ISecT d (BaseT UnitT)) )
          t =  (SecT b (ISecT b (BaseT UnitT)) )
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [  (SinglePV "A"), (SinglePV "C")])))
          exprL = (nullExp (VarE (UVM.var "x"))) 
          exprR = (nullExp (VarE (UVM.var "y"))) 
          expr =  (BundleUnionE exprL exprR)
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , t'),  (UVM.var "y" , t'' ) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : intlisnillannofold" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          t = RecT (UVM.var "X") (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+:  (SecT UVM.Top (   (SecT UVM.Top (BaseT (ℤT InfIPr))) :×: (VarT (UVM.var "X")) ) )))
          t' = (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+: (SecT UVM.Top (  (SecT UVM.Top(BaseT (ℤT InfIPr))) :×: t  ) ) ) )
          expr' =  (AscrE  (nullExp (LE (nullExp (BulE))))  t')
          expr = (AscrE  (nullExp (FoldE (nullExp expr'))) t )
          
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : intlistnillfold" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          t = RecT (UVM.var "X") (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+:  (SecT UVM.Top (   (SecT UVM.Top (BaseT (ℤT InfIPr))) :×: (VarT (UVM.var "X")) ) )))
          expr' =  (LE (nullExp (BulE))) 
          expr = (AscrE  (nullExp (FoldE (nullExp expr'))) t )
          
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , t) ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : intlistconsfold" $
      let η =  Effect {effectInput = UVM.null, effectReveal = UVM.null,  effectMode = UVM.Top}
          τ'' = (SecT UVM.Top (BaseT (ℤT InfIPr)))
          τ' = RecT (UVM.var "X") (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+:  (SecT UVM.Top (   (SecT UVM.Top (BaseT (ℤT InfIPr))) :×: (VarT (UVM.var "X")) ) )))
          t = SecT UVM.Top (τ'' :→: (η UVM.:* (SecT UVM.Top (τ' :→: (η UVM.:* τ')) ))) 
          f = UVM.var "f"
          nvar = (UVM.var "n")
          lvar = (UVM.var "l")
          lst = (UVM.frhs [(VarP nvar), (VarP lvar)] )
       
          expr'' =  (RE (nullExp (ProdE (nullExp (VarE nvar))  (nullExp (VarE lvar)) ) ))
          expr' =(FoldE (nullExp expr'') )
          expr =  (AscrE  (nullExp (LamE (UVM.Some f) lst (nullExp expr')))  t )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , τ') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
      
    it "() : intlisnillunfold" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          t' = RecT (UVM.var "X") (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+:  (SecT UVM.Top (   (SecT UVM.Top (BaseT (ℤT InfIPr))) :×: (VarT (UVM.var "X")) ) )))
          t = (SecT UVM.Top ( (SecT UVM.Top ((BaseT UnitT)))  :+: (SecT UVM.Top (  (SecT UVM.Top(BaseT (ℤT InfIPr))) :×: t'  ) ) ) )
          expr'' =     (LE (nullExp (BulE))) 
          expr' = (AscrE  (nullExp (FoldE (nullExp expr''))) t' )
          expr =  (UnfoldE (nullExp expr') ) 
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [  (UVM.var "x" , t') ])) }) () (synExpR expr))
      in case x of
      UVM.Inr a -> a `shouldBe`  t
      UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e

    it "() : annotatednil" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          b =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) ))
          c = (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A")]) ))
          t''' = (SecT (UVM.Top) (BaseT UnitT))
          t'' = (VarT (UVM.var "X"))
          t' = (SecT (UVM.Top) (ListT 1 t''))
          t = (SecT (UVM.Top) (ListT 1 t'''))
          expr'' =  (AscrE  (nullExp (NilE)) t' )
          expr' = (TLamE (UVM.var "X") (nullExp expr''))
          expr = (TAppE (nullExp expr') t''')
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]),  terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() : parbad" $
      let a =  (UVM.AddTop (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "B")]) ))
          bpse = (PowPSE (UVM.frhs [VarPE (UVM.var "A"), VarPE (UVM.var "C")]) )
          b =  (UVM.AddTop (bpse))
          cpse = PowPSE (UVM.frhs [VarPE (UVM.var "x")])
          c = (UVM.AddTop (cpse))
          t =  (SecT c (BaseT UnitT))
          m = UVM.AddTop (UVM.pow𝐼 (UVM.iter (UVM.frhs [ (SinglePV "A"), (SinglePV "C")])))
          expr' =  (BulE)
          expr = (ParE cpse (nullExp expr')  )
          x  = (evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny m), terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "x" , (SecT UVM.Top (BaseT ℙsT  ))), (UVM.var "D" , (SecT UVM.Top (BaseT 𝔹T ))), (UVM.var "A" , (SecT a (BaseT UnitT ))), (UVM.var "B" , (SecT b (BaseT UnitT ))) ])) }) () (synExpR expr))
      in case x of
        UVM.Inr a -> a `shouldBe`  t
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e
    it "() + () error" $
      let e = PrimE PlusO $ UVM.frhs $ [(nullExp BulE), (nullExp BulE)] in
      let x = evalEM (ER {terPrins =  listToSet (UVM.frhs [UVM.var "A", UVM.var "B", UVM.var "C"]), terModeScope = UVM.dø, terSource = UVM.None, terMode = (AddAny UVM.Top), terEnv = UVM.null}) () (synExpR e) in
      case x of
        UVM.Inl e -> expectationFailure $ Text.unpack $ UVM.frhs $ UVM.ppshow e

   {- it "() : nilexp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙT))) ])) }) () (synExpR (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
     in  case x of
     UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
     AscrE-}
  --  it "() : prinset3exp" $  let x  = (evalEM (ER {terSource = UVM.None, terMode = UVM.Top, terEnv = (UVM.assoc (UVM.frhs [ (UVM.var "A" , (SecT UVM.Top (BaseT ℙsT))) ])) }) () (synExp (PrinSetE (PowPSE (UVM.single𝐿  (VarPE (UVM.var "A")) )) )))
  --   in  case x of
   --  UVM.Inr a -> a `shouldBe`  (SecT UVM.Top  (BaseT ℙsT))
   --(UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (BulE))
   -- (UVM.𝐴 (UVM.SrcCxt {UVM.srcCxtSourceName = "", UVM.srcCxtLocRange = UVM.locRange₀, UVM.srcCxtPrefix = UVM.null, UVM.srcCxtContext = UVM.null, UVM.srcCxtSuffix = UVM.null}) (VarE (UVM.var "A")))
