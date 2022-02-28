module Symphony.Interpreter.Dist.Val where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.Send
import Symphony.Interpreter.NetIO
import Symphony.Interpreter.Error
import Symphony.Interpreter.Share
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Dist.Types

instance Value DistVal where
  type EBV DistVal = ExShare

  introVal   = introValDist
  elimVal    = elimValDist
  unknownVal = unknownValDist
  locateVal  = locateValDist
  inPrins    = inPrinsDist

  shareVal   = shareValDist
  commVal    = commValDist
  flushVal   = flushValDist
  revealVal  = revealValDist

  embedEBV   = embedEBVDist
  primEBV    = primEBVDist

----------------------
--- Intro and Elim ---
----------------------

introValDist ∷ (STACK) ⇒ DistValR → IM DistVal DistVal
introValDist = return ∘ Known

elimValDist ∷ (STACK) ⇒ DistVal → IM DistVal DistValR
elimValDist = \case
  Known v → return v
  Unknown → throwIErrorCxt TypeIError "elimValDist: ⋆" empty𝐿

-----------
--- Par ---
-----------

unknownValDist ∷ (STACK) ⇒ DistVal
unknownValDist = Unknown

locateValDist ∷ (STACK) ⇒ DistVal → IM DistVal DistVal
locateValDist ṽ = return ṽ

inPrinsDist ∷ (STACK) ⇒ 𝑃 PrinVal → IM DistVal 𝔹
inPrinsDist ρ𝑃 = do
  me ← fromSomeCxt *$ askL iCxtMeL
  return $ me ∈ ρ𝑃

-------------
--- Share ---
-------------

shareValDist ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → DistVal → Type → IM DistVal DistVal
shareValDist φ ρvFr ρvsTo ṽ τ = do
  me ← fromSomeCxt *$ askL iCxtMeL
  ṽˢ ← if me ≡ ρvFr then
         sendShareDist φ ρvFr ρvsTo ṽ
       else if me ∈ ρvsTo then
         recvShareDist φ ρvFr ρvsTo τ
       else
         impossibleCxt
  return $ if me ∈ ρvsTo then ṽˢ else unknownValDist

sendShareDist ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → DistVal → IM DistVal DistVal
sendShareDist φ ρvFr ρvsTo ṽ = do
  v  ← elimValDist ṽ
  vˢ ← case v of
         BaseV bv → do
           cbv  ← elimClear bv
           exsh ← withProt φ $ \ p φˢ → ExShare φˢ ^$ share p ρvFr ρvsTo (Inl cbv)
           return $ BaseV $ Encrypted φ ρvsTo exsh
         ProdV ṽ₁ ṽ₂ → do
           ṽ₁ˢ ← sendShareDist φ ρvFr ρvsTo ṽ₁
           ṽ₂ˢ ← sendShareDist φ ρvFr ρvsTo ṽ₂
           return $ ProdV ṽ₁ˢ ṽ₂ˢ
         ListV ṽs → do
           ṽsˢ ← mapM (sendShareDist φ ρvFr ρvsTo) ṽs
           return $ ListV ṽsˢ
         LocV _m (Inr a) → do
           a' ← generateM𝕍Mut (length𝕍Mut a) $ \ i → do
             ṽᵢ ← io $ idx𝕍Mut i a
             sendShareDist φ ρvFr ρvsTo ṽᵢ
           m ← askL iCxtModeL
           return $ LocV m (Inr a')
         _ → todoCxt
  introValDist vˢ

recvShareDist ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Type → IM DistVal DistVal
recvShareDist φ ρvFr ρvsTo τ = do
  vˢ ← case τ of
         BaseT bτ → do
           exsh ← withProt φ $ \ p φˢ → do ExShare φˢ ^$ share p ρvFr ρvsTo (Inr bτ)
           return $ BaseV $ Encrypted φ ρvsTo exsh
         τ₁ :×: τ₂ → do
           ṽ₁ˢ ← recvShareDist φ ρvFr ρvsTo τ₁
           ṽ₂ˢ ← recvShareDist φ ρvFr ρvsTo τ₂
           return $ ProdV ṽ₁ˢ ṽ₂ˢ
         ListT n τ' → do
           let ṽM = recvShareDist φ ρvFr ρvsTo τ'
           ṽsˢ ← list ^$ exchange $ replicate n ṽM
           return $ ListV ṽsˢ
         ArrT n τ' → do
           let ṽM = recvShareDist φ ρvFr ρvsTo τ'
           ṽsˢ ← exchange $ replicate n ṽM
           a ← io $ vecIMut ṽsˢ
           m ← askL iCxtModeL
           return $ LocV m (Inr a)
         _ → todoCxt
  introValDist vˢ

------------
--- Comm ---
------------

commValDist ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → DistVal → Type → IM DistVal DistVal
commValDist ρvFr ρvsTo ṽ τ = do
  me ← fromSomeCxt *$ askL iCxtMeL
  ṽᶜ ← if me ≡ ρvFr then
         sendValDist ρvFr ρvsTo ṽ
       else if me ∈ ρvsTo then
         recvValDist ρvFr ρvsTo τ
       else
         impossibleCxt
  return $ if me ∈ ρvsTo then ṽᶜ else unknownValDist

sendValDist ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → DistVal → IM DistVal DistVal
sendValDist ρvFr ρvsTo ṽ = do
  v  ← elimValDist ṽ
  vᶜ ← case v of
         BaseV bv → do
           cbv ← elimClear bv
           let ρvsRecv = ρvsTo ∖ (single𝑃 ρvFr)
           eachWith (\ ρvTo → sendClearBaseVal ρvFr ρvTo cbv) ρvsRecv
           return v
         ProdV ṽ₁ ṽ₂ → do
           ṽ₁ᶜ ← sendValDist ρvFr ρvsTo ṽ₁
           ṽ₂ᶜ ← sendValDist ρvFr ρvsTo ṽ₂
           return $ ProdV ṽ₁ᶜ ṽ₂ᶜ
         _ → todoCxt
  introValDist vᶜ

recvValDist ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → Type → IM DistVal DistVal
recvValDist ρvFr ρvsTo τ = do
  me ← fromSomeCxt *$ askL iCxtMeL
  vᶜ ← case τ of
         BaseT bτ → do
           cbv ← recvClearBaseVal ρvFr me bτ
           BaseV ^$ introClear cbv
         τ₁ :×: τ₂ → do
           ṽ₁ᶜ ← recvValDist ρvFr ρvsTo τ₁
           ṽ₂ᶜ ← recvValDist ρvFr ρvsTo τ₂
           return $ ProdV ṽ₁ᶜ ṽ₂ᶜ
         _ → todoCxt
  introValDist vᶜ

--- Flush

flushValDist ∷ (STACK) ⇒ PrinVal → PrinVal → IM DistVal ()
flushValDist ρvFr ρvTo = do
  net ← getOrMkChannel ρvFr ρvTo
  io $ netIOFlush net

--------------
--- Reveal ---
--------------

revealValDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → DistVal → Type → IM DistVal DistVal
revealValDist φ ρvsFr ρvTo ṽ _τ = do
  me ← fromSomeCxt *$ askL iCxtMeL
  ṽᵣ ← revealDist φ ρvsFr ρvTo ṽ
  return $ if me ≡ ρvTo then ṽᵣ else Unknown

revealDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → DistVal → IM DistVal DistVal
revealDist φ ρvsFr ρvTo ṽ = do
  v  ← elimValDist ṽ
  vᵣ ← case v of
    BaseV bv → do
      xsh ← elimEncrypted φ ρvsFr bv
      withProt φ $ \ p φˢ → do
        sh ← elimExShare φˢ xsh
        cbv ← reveal p ρvsFr ρvTo sh
        return $ BaseV $ Clear cbv
    ProdV ṽₗ ṽᵣ → do
      ṽₗʳ ← revealDist φ ρvsFr ρvTo ṽₗ
      ṽᵣʳ ← revealDist φ ρvsFr ρvTo ṽᵣ
      return $ ProdV ṽₗʳ ṽᵣʳ
    _ → todoCxt
  introValDist vᵣ

--- Embed

embedEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM DistVal ExShare
embedEBVDist φ ρ𝑃 cbv = withProt φ $ \ p φˢ → do
  sh ← embed p ρ𝑃 cbv
  return $ ExShare φˢ sh

--- Prim

primEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 ExShare → IM DistVal ExShare
primEBVDist φ ρ𝑃 op ebvs = withProt φ $ \ p φˢ → do
  shs ← mapM (elimExShare φˢ) ebvs
  sh  ← prim p ρ𝑃 op shs
  return $ ExShare φˢ sh
