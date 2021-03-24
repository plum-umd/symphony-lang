module PSL.Interpreter.Share where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Error

import PSL.Interpreter.Plain ()
import PSL.Interpreter.YaoN ()

withProt ∷ Prot → (∀ (p ∷ Prot). (Protocol p) ⇒ P p → SProt p → IM b) → IM b
withProt φ k = case φ of
  PlainP → k P SPlainP
  YaoNP  → k P SYaoNP
--  Yao2P  → k P SYao2P
--  BGWP   → k P SBGWP
--  GMWP   → k P SGMWP
--  BGVP   → k P SBGVP
--  SPDZP  → k P SSPDZP
--  AutoP  → k P SAutoP
  _      → throwIErrorCxt NotImplementedIError "withProt: φ" $ frhs [ ("φ", pretty φ) ]

sameProt ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Prot → SProt p → IM ()
sameProt φ sp = case (φ, sp) of
  (PlainP, SPlainP) → return ()
  (YaoNP , SYaoNP ) → return ()
--  (Yao2P , SYao2P ) → return ()
--  (BGWP  , SBGWP  ) → return ()
--  (GMWP  , SGMWP  ) → return ()
--  (BGVP  , SBGVP  ) → return ()
--  (SPDZP , SSPDZP ) → return ()
--  (AutoP , SAutoP ) → return ()
  _ → throwIErrorCxt TypeIError "sameProt: φ ≢ sp" $ frhs [ ("φ", pretty φ), ("sp", pretty sp) ]

unwrapShare ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ SProt p → Share → IM (ProtocolVal p)
unwrapShare sp₁ (Share sp₂ pv) = case deq sp₁ sp₂ of
  NoDEq → throwIErrorCxt TypeIError "unwrapShare: deq sp₁ sp₂ ≡ NoDEq" $ frhs
          [ ("sp₁", pretty sp₁)
          , ("sp₂", pretty sp₂)
          ]
  YesDEq → return pv
