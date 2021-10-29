module Allyn.Interpreter.Seq.Val where

import UVMHS
import AddToUVMHS

import Allyn.Syntax
import Allyn.Interpreter.Types
import Allyn.Interpreter.Operations
import Allyn.Interpreter.BaseVal
import Allyn.Interpreter.Seq.Types
import Allyn.Interpreter.Pretty ()
import Allyn.Interpreter.Lens
import Allyn.Interpreter.Error

import Allyn.Interpreter.Primitives

instance Value SeqVal where
  type EBV SeqVal = ClearBaseVal

  introVal   = introSeqVal
  elimVal    = elimSeqVal
  unknownVal = unknownSeqVal
  locateVal  = locateSeqVal
  inPrins    = inPrinsSeq

  shareVal  = shareValSeq
  commVal   = commValSeq
  flushVal  = flushValSeq
  revealVal = revealValSeq

  embedEBV  = embedEBVSeq
  primEBV   = primEBVSeq

----------------------
--- Val Operations ---
----------------------

introSeqValMode ∷ (STACK) ⇒ Mode → SeqValR → IM SeqVal SeqVal
introSeqValMode m v = return $ Located m v

introSeqVal ∷ (STACK) ⇒ SeqValR → IM SeqVal SeqVal
introSeqVal v = do
  m ← askL iCxtModeL
  introSeqValMode m v

elimSeqValMode ∷ (STACK) ⇒ Mode → SeqVal → IM SeqVal SeqValR
elimSeqValMode m = \case
    Located l v → do
      guardErr (m ⊑ l) $
        throwIErrorCxt TypeIError "elimSeqValMode: m ⋢ l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      return v
    Unknown → throwIErrorCxt TypeIError "elimSeqValMode: ⋆" empty𝐿

elimSeqVal ∷ (STACK) ⇒ SeqVal → IM SeqVal SeqValR
elimSeqVal ṽ = do
  m ← askL iCxtModeL
  elimSeqValMode m ṽ

unknownSeqVal ∷ (STACK) ⇒ SeqVal
unknownSeqVal = Unknown

locateSeqVal ∷ (STACK) ⇒ SeqVal → IM SeqVal SeqVal
locateSeqVal ṽ = do
  m ← askL iCxtModeL
  case ṽ of
    Located l v → do
      let m' = m ⊓ l
      if m' ≢ bot then Located m' ^$ locateValR v else return Unknown
    Unknown → return Unknown

inPrinsSeq ∷ (STACK) ⇒ 𝑃 PrinVal → IM SeqVal 𝔹
inPrinsSeq _ρ𝑃 = return True

shareValSeq ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → SeqVal → Type → IM SeqVal SeqVal
shareValSeq φ ρvFr ρvsTo ṽ τ = do
  v  ← elimSeqValMode (AddTop $ single𝑃 ρvFr) ṽ
  vˢ ← case v of
         BaseV bv → do
           cbv ← elimClear bv
           return $ BaseV $ Encrypted φ ρvsTo cbv
         ProdV ṽₗ ṽᵣ → do
           τₗ :* τᵣ ← error𝑂 (view pairTL τ) $
                      throwIErrorCxt TypeIError "shareValSeq: view pairTL τ ≡ None" $ frhs
                      [ ("τ", pretty τ)
                      ]
           ṽₗˢ ← shareValSeq φ ρvFr ρvsTo ṽₗ τₗ
           ṽᵣˢ ← shareValSeq φ ρvFr ρvsTo ṽᵣ τᵣ
           return $ ProdV ṽₗˢ ṽᵣˢ
         SumV bv ṽₗ ṽᵣ → do
           τₗ :* τᵣ ← error𝑂 (view sumTL τ) $
                      throwIErrorCxt TypeIError "shareValSeq: view sumTL τ ≡ None" $ frhs
                      [ ("τ", pretty τ)
                      ]
           cbv ← elimClear bv
           let bvˢ = Encrypted φ ρvsTo cbv
           ṽₗˢ ← shareValSeq φ ρvFr ρvsTo ṽₗ τₗ
           ṽᵣˢ ← shareValSeq φ ρvFr ρvsTo ṽᵣ τᵣ
           return $ SumV bvˢ ṽₗˢ ṽᵣˢ
         ListV ṽs → do
           _ :* τ' ← error𝑂 (view listTL τ) $
                     throwIErrorCxt TypeIError "shareValSeq: view listTL τ ≡ None" $ frhs
                      [ ("τ", pretty τ)
                      ]
           ṽsˢ ← mapM (\ ṽ' → shareValSeq φ ρvFr ρvsTo ṽ' τ') ṽs
           return $ ListV ṽsˢ
         LocV _m (Inr a) → do
           _ :* τ' ← error𝑂 (view arrTL τ) $
                     throwIErrorCxt TypeIError "shareValSeq: view arrTL τ ≡ None" $ frhs
                      [ ("τ", pretty τ)
                      ]
           a' ← generateM𝕍Mut (length𝕍Mut a) $ \ i → do
             ṽᵢ ← io $ idx𝕍Mut i a
             shareValSeq φ ρvFr ρvsTo ṽᵢ τ'
           m ← askL iCxtModeL
           return $ LocV m (Inr a')
         DefaultV → return $ defaultClearValR τ
         _ → throwIErrorCxt NotImplementedIError "shareValSeq" $ frhs
             [ ("v", pretty v) ]
  introSeqValMode (AddTop ρvsTo) vˢ

commValSeq ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → SeqVal → Type → IM SeqVal SeqVal
commValSeq ρvFr ρvsTo ṽ _τ = do
  v  ← elimSeqValMode (AddTop $ single𝑃 ρvFr) ṽ
  vˢ ← case v of
         BaseV bv → do
           cbv ← elimClear bv
           return $ BaseV $ Clear cbv
         ProdV ṽₗ ṽᵣ → do
           ṽₗˢ ← commValSeq ρvFr ρvsTo ṽₗ _τ
           ṽᵣˢ ← commValSeq ρvFr ρvsTo ṽᵣ _τ
           return $ ProdV ṽₗˢ ṽᵣˢ
         _ → todoCxt
  introSeqValMode (AddTop ρvsTo) vˢ

flushValSeq ∷ (STACK) ⇒ PrinVal → PrinVal → IM SeqVal ()
flushValSeq _ρvFr _ρvTo = return ()

revealValSeq ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → SeqVal → Type → IM SeqVal SeqVal
revealValSeq φ ρvsFr ρvTo ṽ _τ = do
  v  ← elimSeqValMode (AddTop ρvsFr) ṽ
  vʳ ← case v of
         BaseV bv → do
           cbv ← elimEncrypted φ ρvsFr bv
           return $ BaseV $ Clear cbv
         ProdV ṽₗ ṽᵣ → do
           ṽₗˢ ← revealValSeq φ ρvsFr ρvTo ṽₗ _τ
           ṽᵣˢ ← revealValSeq φ ρvsFr ρvTo ṽᵣ _τ
           return $ ProdV ṽₗˢ ṽᵣˢ
         ListV ṽs → do
           ṽsˢ ← mapM (\ ṽ' → revealValSeq φ ρvsFr ρvTo ṽ' _τ) ṽs
           return $ ListV ṽsˢ
         _ → todoCxt
  introSeqValMode (AddTop $ single𝑃 ρvTo) vʳ

embedEBVSeq ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM SeqVal ClearBaseVal
embedEBVSeq _φ _ρ𝑃 cbv = return cbv

primEBVSeq ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 ClearBaseVal → IM SeqVal ClearBaseVal
primEBVSeq _φ _ρ𝑃 op cbvs = evalPrimClearBaseVal op cbvs
