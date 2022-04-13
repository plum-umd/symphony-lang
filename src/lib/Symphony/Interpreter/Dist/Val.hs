module Symphony.Interpreter.Dist.Val where

import Symphony.Prelude

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.Send
import Symphony.Interpreter.Channel
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
shareValDist φ ρvFr ρvsTo ṽ τ =
  withProt φ $ \ φˢ → do
  me ← fromSomeCxt *$ askL iCxtMeL
  when (me ≡ ρvFr) $ do
    chansTo ← pmapM getOrMkChannel ρvsTo
    sendShareValDist φˢ chansTo ṽ
  if me ∈ ρvsTo then do
    chanFr ← getOrMkChannel ρvFr
    recvShareValDist φˢ ρvsTo chanFr τ
  else return unknownValDist

sendShareValDist ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 Channel → DistVal → IM DistVal ()
sendShareValDist φˢ chansTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      cbv ← elimClear bv
      sendShare φˢ chansTo cbv
    _ → todoCxt

recvShareValDist ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 PrinVal → Channel → Type → IM DistVal DistVal
recvShareValDist φˢ ρvsC chanFr τ = do
  v ← case τ of
        BaseT bτ → do
          exsh ← ExShare φˢ ^$ recvShare φˢ ρvsC chanFr bτ
          return $ BaseV $ Encrypted (protFrSProt φˢ) ρvsC exsh
        _ → todoCxt
  introValDist v

------------
--- Comm ---
------------

commValDist ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → DistVal → Type → IM DistVal DistVal
commValDist ρvFr ρvsTo ṽ τ = do
  me ← fromSomeCxt *$ askL iCxtMeL
  when (me ≡ ρvFr) $ do
    chansTo ← pmapM getOrMkChannel ρvsTo
    sendValDist chansTo ṽ
  if me ∈ ρvsTo then do
    chanFr ← getOrMkChannel ρvFr
    recvValDist chanFr τ
  else return unknownValDist

sendValDist ∷ (STACK) ⇒ 𝑃 Channel → DistVal → IM DistVal ()
sendValDist chansTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      cbv ← elimClear bv
      eachWith (\ chanTo → sendClearBaseVal chanTo cbv) chansTo
    _ → todoCxt

recvValDist ∷ (STACK) ⇒ Channel → Type → IM DistVal DistVal
recvValDist chanFr τ = do
  v ← case τ of
        BaseT bτ → do
          cbv ← recvClearBaseVal chanFr bτ
          BaseV ^$ introClear cbv
        _ → todoCxt
  introValDist v

--- Flush

flushValDist ∷ (STACK) ⇒ PrinVal → IM DistVal ()
flushValDist ρvOther = do
  chan ← getOrMkChannel ρvOther
  channelFlush chan

--------------
--- Reveal ---
--------------

revealValDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → DistVal → Type → IM DistVal DistVal
revealValDist φ ρvsFr ρvTo ṽ τ =
  withProt φ $ \ φˢ → do
  me ← fromSomeCxt *$ askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    chanTo ← getOrMkChannel ρvTo
    sendRevealValDist φˢ ρvsFr chanTo ṽ
  if me ≡ ρvTo then do
    chansFr ← pmapM getOrMkChannel ρvsFr
    recvRevealValDist φˢ chansFr τ
  else return unknownValDist

sendRevealValDist ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 PrinVal → Channel → DistVal → IM DistVal ()
sendRevealValDist φˢ ρvsC chanTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      exsh ← elimEncrypted (protFrSProt φˢ) ρvsC bv
      sh   ← elimExShare φˢ exsh
      sendReveal φˢ ρvsC chanTo sh
    _ → todoCxt

recvRevealValDist ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 Channel → Type → IM DistVal DistVal
recvRevealValDist φˢ chansFr τ = do
  v ← case τ of
        BaseT bτ → do
          cbv ← recvReveal φˢ chansFr bτ
          return $ BaseV $ Clear cbv
        _ → todoCxt
  introValDist v

--- Embed

embedEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM DistVal ExShare
embedEBVDist φ ρvsC cbv =
  withProt φ $ \ φˢ → do
  sh ← embed φˢ ρvsC cbv
  return $ ExShare φˢ sh

--- Prim

primEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 ExShare → IM DistVal ExShare
primEBVDist φ ρvsC op ebvs =
  withProt φ $ \ φˢ → do
  shs ← mapM (elimExShare φˢ) ebvs
  sh  ← prim φˢ ρvsC op shs
  return $ ExShare φˢ sh
