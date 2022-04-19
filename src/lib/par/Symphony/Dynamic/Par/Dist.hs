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
shareVal φ ρvsFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    shareValSend φ ρvsFr ρvsTo ṽ
  if me ∈ ρvsTo then do
    shareValRecv φ ρvsFr ρvsTo τ
  else return unknownValDist

shareValSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → IM Val ()
shareValSend φ ρvsFr ρvsTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv    → elimBaseVal ρvsFr (shareSend φ ρvsFr ρvsTo) (reshareSend φ ρvsFr ρvsTo) bv
    ProdV ṽ₁ ṽ₂ → do
      shareValSend φ ρvsFr ρvsTo ṽ₁
      shareValSend φ ρvsFr ρvsTo ṽ₂
    _ → todoCxt

shareValRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Type → IM Val Val
shareValRecv φₑ ρvsFr ρvsTo τ = do
  v ← case τ of
        SecT _ (BaseT bτ)                → BaseV ^$ EncV ρvsTo ^$ shareRecv φₑ ρvsFr ρvsTo bτ -- TODO(ins): rough and ready
        ShareT φₐ _ (BaseT bτ) | φₑ ≡ φₐ → BaseV ^$ EncV ρvsTo ^$ reshareRecv φₐ ρvsFr ρvsTo bτ
        τ₁ :×: τ₂ → do
          ṽ₁ ← shareValRecv φₑ ρvsFr ρvsTo τ₁
          ṽ₂ ← shareValRecv φₑ ρvsFr ρvsTo τ₂
          return $ ProdV ṽ₁ ṽ₂
        _ → todoCxt
  return $ KnownV v

shareSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → ClearBaseVal → IM Val ()
shareSend φ ρvsFr ρvsTo cbv = case φ of
  GMWP → shareSendGmw ρvsFr ρvsTo cbv
  _    → todoCxt

reshareSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → EncBaseVal → IM Val ()
reshareSend φ ρvsFr ρvsTo ebv = case φ of
  GMWP → do
    gmw ← elimGmw ebv
    reshareSendGmw ρvsFr ρvsTo gmw
  _    → todoCxt

shareRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val EncBaseVal
shareRecv φ ρvsFr ρvsTo bτ = case φ of
  GMWP → GmwV ^$ shareRecvGmw ρvsTo ρvsFr bτ
  _    → todoCxt

reshareRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val EncBaseVal
reshareRecv φ ρvsFr ρvsTo bτ = case φ of
  GMWP → GmwV ^$ reshareRecvGmw ρvsTo ρvsFr bτ
  _    → todoCxt

------------
--- Comm ---
------------

commVal ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvFr ρvsTo ṽ τ = todoCxt

--------------
--- Reveal ---
--------------

revealVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
revealVal φ ρvsFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    revealValSend φ ρvsFr ρvsTo ṽ
  if me ∈ ρvsTo then do
    revealValRecv φ ρvsFr ρvsTo τ
  else return unknownValDist

revealValSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → IM Val ()
revealValSend φ ρvsFr ρvsTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv    → do
      ebv ← elimEnc ρvsFr bv
      revealSend φ ρvsFr ρvsTo ebv
    ProdV ṽ₁ ṽ₂ → do
      revealValSend φ ρvsFr ρvsTo ṽ₁
      revealValSend φ ρvsFr ρvsTo ṽ₂
    _ → todoCxt

revealValRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Type → IM Val Val
revealValRecv φ ρvsFr ρvsTo τ = do
  v ← case τ of
        BaseT bτ  → BaseV ^$ ClearV ^$ revealRecv φ ρvsFr ρvsTo bτ
        τ₁ :×: τ₂ → do
          ṽ₁ ← revealValRecv φ ρvsFr ρvsTo τ₁
          ṽ₂ ← revealValRecv φ ρvsFr ρvsTo τ₂
          return $ ProdV ṽ₁ ṽ₂
        _ → todoCxt
  return $ KnownV v

revealSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → EncBaseVal → IM Val ()
revealSend φ ρvsFr ρvsTo ebv = case φ of
  GMWP → do
    gmw ← elimGmw ebv
    revealSendGmw ρvsFr ρvsTo gmw
  _ → todoCxt

revealRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val ClearBaseVal
revealRecv φ ρvsFr ρvsTo bτ = case φ of
  GMWP → revealRecvGmw ρvsFr ρvsTo bτ
  _    → todoCxt

--- Embed

embedEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM Val EncBaseVal
embedEBVDist φ ρvs cbv = case φ of
  GMWP → GmwV ^$ embedGmw ρvs cbv
  _ → todoCxt

--- Prim

primEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 EncBaseVal → IM Val EncBaseVal
primEBVDist φ ρvs op ebvs = case φ of
  GMWP → do
    shs ← mapM elimGmw ebvs
    GmwV ^$ primGmw ρvs op shs
  _ → todoCxt
