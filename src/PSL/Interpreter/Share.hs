module PSL.Interpreter.Share where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Error

import PSL.Interpreter.YaoN ()

withProt ∷ Prot → (∀ (p ∷ Prot). (Protocol p) ⇒ P p → SProt p → IM b) → IM b
withProt φ k = case φ of
  YaoN_P → k P SYaoN_P
  _      → undefined

sameProt ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Prot → SProt p → IM ()
sameProt φ sp = case (φ, sp) of
  (YaoN_P, SYaoN_P) → return ()
  _ → throwIErrorCxt TypeIError "sameProt: φ ≢ sp" $ frhs [ ("φ", pretty φ), ("sp", pretty sp) ]


unwrapShare ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ SProt p → Share → IM (ProtocolVal p)
unwrapShare sp₁ (Share sp₂ pv) = case deq sp₁ sp₂ of
  NoDEq → throwIErrorCxt TypeIError "unwrapShare: deq sp₁ sp₂ ≡ NoDEq" $ frhs
          [ ("sp₁", pretty sp₁)
          , ("sp₂", pretty sp₂)
          ]
  YesDEq → return pv
