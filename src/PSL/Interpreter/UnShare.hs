module PSL.Interpreter.UnShare where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import PSL.Interpreter.Access
import PSL.Interpreter.Val
import PSL.Interpreter.MPCVal
import PSL.Interpreter.Primitives
import PSL.Interpreter.Share


--------------------------------
--- Operations on [UnShare]s ---
--------------------------------

primUnShare ∷ (STACK) ⇒ Op → 𝐿 UnShare → IM UnShare
primUnShare op uss = do
  vsorv̂s ← unwrapUnShares uss
  case vsorv̂s of
    Inl vs → do
      bvs ← error𝑂 (mapMOn vs $ view baseVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn vs $ view baseVL ≡ None" $ frhs
                                              [ ("vs", pretty vs)
                                              ])
      bv' ← interpPrim op bvs
      return $ NotShared $ BaseV bv'
    Inr (φ :* ρvs :* v̂s) → do
      shs ← error𝑂 (mapMOn v̂s $ view baseMVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn v̂s $ view baseMVL ≡ None" $ frhs
                                              [ ("v̂s", pretty v̂s)
                                              ])
      sh' ← withProt φ $ \ p sp → do
        pvs ← mapMOn shs $ \ sh → unwrapShare sh sp
        pv' ← exePrim p op pvs
        return $ Share sp pv'
      return $ Shared φ ρvs $ BaseMV sh'

notUnShare ∷ (STACK) ⇒ UnShare → IM UnShare
notUnShare us = primUnShare NotO $ frhs [ us ]

sumUnShare ∷ (STACK) ⇒ UnShare → UnShare → IM UnShare
sumUnShare us₁ us₂ = do
  vsorv̂s ← unwrapUnShares $ frhs [ us₁, us₂ ]
  case vsorv̂s of
    Inl (v₁ :& v₂ :& Nil) → do
      v' ← sumVal v₁ v₂
      return $ NotShared v'
    Inr (φ :* ρvs :* (v̂₁ :& v̂₂ :& Nil)) → do
      v̂' ← withProt φ $ sumMPCVal v̂₁ v̂₂
      return $ Shared φ ρvs v̂'

--------------------------------
--- Prisms(ish) of [UnShare] ---
--------------------------------

viewPairUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewPairUnShare = \case
  NotShared (PairV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  Shared φ ρvs (PairMV v̂₁ v̂₂) → return $ Shared φ ρvs v̂₁ :* Shared φ ρvs v̂₂
  _ → abort
