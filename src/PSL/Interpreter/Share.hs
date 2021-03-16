module PSL.Interpreter.Share where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Error

withShare ∷ Share → (∀ p. (Protocol p) ⇒ P p → SProt p → ProtocolVal p → IM b) → IM b
withShare (Share sp pv) k = k P sp pv

withShares
  ∷ 𝐿 Share
  → IM b
  → (∀ p. (Protocol p) ⇒ P p → SProt p → 𝐿 (ProtocolVal p) → IM b)
  → IM b
withShares shs kEmpty kNotEmpty = case shs of
  Nil → kEmpty
  Share sp pv :& shs' → do
    pvs ← error𝑂 (sameProts sp shs') $ throwIErrorCxt TypeIError "withShares: sameProts sp shs' ≡ None" $ frhs
      [ ("sp", pretty sp)
      , ("shs'", pretty shs')
      ]
    kNotEmpty P sp $ pv :& pvs

sameProts ∷ SProt p → 𝐿 Share → 𝑂 (𝐿 (ProtocolVal p))
sameProts sp = mfoldrFromWith null $ \ (Share sp' pv) pvs →
  case deq sp sp' of
    NoDEq → abort
    YesDEq → return $ pv :& pvs
