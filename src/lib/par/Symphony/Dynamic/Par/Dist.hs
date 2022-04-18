module Symphony.Dynamic.Par.Dist where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Send
import Symphony.Dynamic.Par.Channel
import Symphony.Dynamic.Par.Error

import Symphony.Dynamic.Par.GMW

----------------------
--- Intro and Elim ---
----------------------

introValDist ∷ (STACK) ⇒ ValR → IM Val Val
introValDist = return ∘ KnownV

elimValDist ∷ (STACK) ⇒ Val → IM Val ValR
elimValDist = \case
  KnownV v → return v
  UnknownV → throwIErrorCxt TypeIError "elimValDist: ⋆" empty𝐿

-----------
--- Par ---
-----------

unknownValDist ∷ (STACK) ⇒ Val
unknownValDist = UnknownV

inPrinsDist ∷ (STACK) ⇒ 𝑃 PrinVal → IM Val 𝔹
inPrinsDist ρ𝑃 = do
  me ← askL iCxtMeL
  return $ me ∈ ρ𝑃

-------------
--- Share ---
-------------

shareVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
shareVal φ ρvsFr ρvsTo ṽ τ = undefined
{-  do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    chansTo ← getOrMkChannels ρvsTo
    shareValTo φ ρvsFr chansTo ṽ
  if me ∈ ρvsTo then do
    chansFr ← getOrMkChannels ρvsFr
    shareValFr φ chansFr ρvsTo τ
  else return unknownValDist

shareValTo ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → (PrinVal ⇰ Channel) → Val → IM Val ()
shareValTo φ ρvsFr chansTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      elimBaseVal φ ρvsFr (sendShareValClear φ ρvsFr chansTo) (sendShareValEnc φ ρvsFr chansTo) bv
    _ → todoCxt

sendShareValClear ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → (PrinVal ⇰ Channel) → ClearBaseVal → IM Val ()
sendShareValClear φ ρvsFr chansTo cbv = undefined

shareValFr ∷ (STACK) ⇒ Prot → (PrinVal ⇰ Channel) → 𝑃 PrinVal → Type → IM Val Val
shareValFr φ chansFr ρvsTo τ = undefined
  v ← case τ of
        BaseT bτ → do
          exsh ← ExShare φˢ ^$ recvShare φˢ ρvsC chansFr bτ
          return $ BaseV $ Encrypted (protFrSProt φˢ) ρvsC exsh
        _ → todoCxt
  introValDist v
-}
------------
--- Comm ---
------------

commVal ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvFr ρvsTo ṽ τ = undefined
{-
  do
  me ← askL iCxtMeL
  when (me ≡ ρvFr) $ do
    chansTo ← pmapM getOrMkChannel ρvsTo
    sendValDist chansTo ṽ
  if me ∈ ρvsTo then do
    chanFr ← getOrMkChannel ρvFr
    recvValDist chanFr τ
  else return unknownValDist

sendValDist ∷ (STACK) ⇒ 𝑃 Channel → Val → IM Val ()
sendValDist chansTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      cbv ← elimClear bv
      eachWith (\ chanTo → sendClearBaseVal chanTo cbv) chansTo
    _ → todoCxt

recvValDist ∷ (STACK) ⇒ Channel → Type → IM Val Val
recvValDist chanFr τ = do
  v ← case τ of
        BaseT bτ → do
          cbv ← recvClearBaseVal chanFr bτ
          BaseV ^$ introClear cbv
        _ → todoCxt
  introValDist v

--- Flush

flushValDist ∷ (STACK) ⇒ PrinVal → IM Val ()
flushValDist ρvOther = do
  chan ← getOrMkChannel ρvOther
  channelFlush chan
-}
--------------
--- Reveal ---
--------------

revealVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
revealVal φ ρvsFr ρvsTo ṽ τ = undefined
{-  withProt φ $ \ φˢ → do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    chanTo ← getOrMkChannel ρvTo
    sendRevealValDist φˢ ρvsFr chanTo ṽ
  if me ≡ ρvTo then do
    chansFr ← pmapM getOrMkChannel ρvsFr
    recvRevealValDist φˢ chansFr τ
  else return unknownValDist

sendRevealValDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Channel → Val → IM Val ()
sendRevealValDist φ ρvsC chanTo ṽ = do
  v ← elimValDist ṽ
  case v of
    BaseV bv → do
      exsh ← elimEncrypted (protFrSProt φˢ) ρvsC bv
      sh   ← elimExShare φˢ exsh
      sendReveal φˢ ρvsC chanTo sh
    _ → todoCxt

recvRevealValDist ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 Channel → Type → IM Val Val
recvRevealValDist φˢ chansFr τ = do
  v ← case τ of
        BaseT bτ → do
          cbv ← recvReveal φˢ chansFr bτ
          return $ BaseV $ Clear cbv
        _ → todoCxt
  introValDist v
-}
--- Embed

embedEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM Val EncBaseVal
embedEBVDist φ ρvsC cbv = undefined
{-  withProt φ $ \ φˢ → do
  sh ← embed φˢ ρvsC cbv
  return $ ExShare φˢ sh -}

--- Prim

primEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 EncBaseVal → IM Val EncBaseVal
primEBVDist φ ρvsC op ebvs = case φ of
  GMWP → do
    gmwSession ← getOrMkGmwSession ρvsC
    shs ← mapM elimGmw ebvs
    sh  ← io $ primGmw gmwSession op shs
    return $ GmwV sh
  _ → todoCxt
