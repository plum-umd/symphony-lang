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

share ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
share φ ρvFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ≡ ρvFr) $ do
    shareSend φ ρvFr ρvsTo ṽ
  if me ∈ ρvsTo then do
    shareRecv φ ρvFr ρvsTo τ
  else return unknownValDist

shareSend ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Val → IM Val ()
shareSend φ ρvFr ρvsTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → do
      cbv ← elimClear bv
      case φ :* cbv of
        GMWP :* BulCV    → return ()
        GMWP :* BoolCV b → do
          prg   ← getPrg
          chans ← getChannels ρvsTo
          gmwShareSendBool prg chans b
        _ → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      shareSend φ ρvFr ρvsTo ṽ₁
      shareSend φ ρvFr ρvsTo ṽ₂
    _ → todoCxt

shareRecv ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Type → IM Val Val
shareRecv φ ρvFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ EncV ρvsTo ^$ case φ :* bτ of
    GMWP :* UnitT → return $ BulEV GmwEBul
    GMWP :* 𝔹T    → BoolEV ^$ GmwEB ^$ do
      gmw  ← getOrMkGmw ρvsTo
      chan ← getChannel ρvFr
      gmwShareRecvBool gmw chan
    _ → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← shareRecv φ ρvFr ρvsTo τ₁
    ṽ₂ ← shareRecv φ ρvFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  _ → todoCxt

------------
--- Comm ---
------------

commVal ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvFr ρvsTo ṽ τ = todoCxt

--------------
--- Reveal ---
--------------

reveal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Val → Type → IM Val Val
reveal φ ρvsFr ρvTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    revealSend φ ρvsFr ρvTo ṽ
  if me ≡ ρvTo then do
    revealRecv φ ρvsFr ρvTo τ
  else return unknownValDist

revealSend ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Val → IM Val ()
revealSend φ ρvsFr ρvTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → do
      ebv ← elimEnc ρvsFr bv
      case φ :* ebv of
        GMWP :* BulEV  ebul → do
          elimGmwBul ebul
        GMWP :* BoolEV eb → do
          gmw  ← getOrMkGmw ρvsFr
          chan ← getChannel ρvTo
          b    ← elimGmwBool eb
          gmwRevealSendBool gmw chan b
        _ → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      revealSend φ ρvsFr ρvTo ṽ₁
      revealSend φ ρvsFr ρvTo ṽ₂
    _ → todoCxt

revealRecv ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Type → IM Val Val
revealRecv φ ρvsFr ρvTo τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ ClearV ^$ case φ :* bτ of
    GMWP :* UnitT → return BulCV
    GMWP :* 𝔹T    → BoolCV ^$ do
      chans ← getChannels ρvsFr
      gmwRevealRecvBool chans
    _ → todoCxt
  τ₁ :×: τ₂ → do
      ṽ₁ ← revealRecv φ ρvsFr ρvTo τ₁
      ṽ₂ ← revealRecv φ ρvsFr ρvTo τ₂
      return $ ProdV ṽ₁ ṽ₂
  _ → todoCxt

--- Embed

embedEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → ClearBaseVal → IM Val EncBaseVal
embedEBVDist φ ρvs cbv = case φ :* cbv of
  GMWP :* BulCV    → return $ BulEV GmwEBul
  GMWP :* BoolCV b → do
    gmw ← getOrMkGmw ρvs
    BoolEV ^$ GmwEB ^$ gmwLitBool gmw b
  _ → todoCxt

--- Prim

primEBVDist ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → Op → 𝐿 EncBaseVal → IM Val EncBaseVal
primEBVDist φ ρvs op ebvs = case φ :* op :* tohs ebvs of
  GMWP :* AndO :* [ BoolEV eb1 , BoolEV eb2 ] → do
    gmw ← getOrMkGmw ρvs
    b1 ← elimGmwBool eb1
    b2 ← elimGmwBool eb2
    BoolEV ^$ GmwEB ^$ gmwAndBool gmw b1 b2
  _ → todoCxt
