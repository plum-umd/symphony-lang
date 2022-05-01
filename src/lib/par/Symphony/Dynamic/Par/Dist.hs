module Symphony.Dynamic.Par.Dist where

import Symphony.Prelude
import qualified Prelude as HS

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

shareVal ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
shareVal φ ρvFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ≡ ρvFr) $ do
    shareSendVal φ ρvFr ρvsTo ṽ
    chans ← list ^$ values ^$ getChannels ρvsTo
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    shareRecvVal φ ρvFr ρvsTo τ
  else return unknownValDist

shareSendVal ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Val → IM Val ()
shareSendVal φ ρvFr ρvsTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → case φ of
      GMWP → do
        prg   ← getPrg
        chans ← list ^$ values ^$ getChannels ρvsTo
        case bv of
          BoolV bool  → gmwShareSendBool prg chans    *$ elimClearBV bool
          NatV pr nat → gmwShareSendNat  prg chans pr *$ elimClearNV nat
          IntV pr int → gmwShareSendInt  prg chans pr *$ elimClearZV int
          _           → todoCxt
      _    → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      shareSendVal φ ρvFr ρvsTo ṽ₁
      shareSendVal φ ρvFr ρvsTo ṽ₂
    ListV ṽs → do
      commSendVal ρvFr ρvsTo $ KnownV $ BaseV $ NatV iprDefault $ ClearNV $ count ṽs
      eachWith (shareSendVal φ ρvFr ρvsTo) ṽs
    LocV _m (Inr a) → do
      commSendVal ρvFr ρvsTo $ KnownV $ BaseV $ NatV iprDefault $ ClearNV $ HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachWith (shareSendVal φ ρvFr ρvsTo) ṽs
    _           → todoCxt

shareRecvVal ∷ (STACK) ⇒ Prot → PrinVal → 𝑃 PrinVal → Type → IM Val Val
shareRecvVal φ ρvFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ  → BaseV ^$ case φ of
    GMWP → do
      gmw  ← getOrMkGmw ρvsTo
      chan ← getChannel ρvFr
      case bτ of
        𝔹T    → BoolV   ^$ EncBV ρvsTo ^$ GmwB ^$ gmwShareRecvGmwBool gmw chan
        ℕT pr → NatV pr ^$ EncNV ρvsTo ^$ GmwN ^$ gmwShareRecvGmwNat gmw chan pr
        ℤT pr → IntV pr ^$ EncZV ρvsTo ^$ GmwZ ^$ gmwShareRecvGmwInt gmw chan pr
        _     → todoCxt
    _    → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← shareRecvVal φ ρvFr ρvsTo τ₁
    ṽ₂ ← shareRecvVal φ ρvFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  ListT τ' → do
    _ :* len_nat ← elimNat *$ elimBase *$ elimKnown *$ commRecvVal ρvFr ρvsTo $ BaseT $ ℕT iprDefault
    len ← elimClearNV len_nat
    let ṽM = shareRecvVal φ ρvFr ρvsTo τ'
    ṽs ← list ^$ exchange $ replicate len ṽM
    return $ ListV ṽs
  ArrT τ' → do
    _ :* len_nat ← elimNat *$ elimBase *$ elimKnown *$ commRecvVal ρvFr ρvsTo $ BaseT $ ℕT iprDefault
    len ← elimClearNV len_nat
    let ṽM = shareRecvVal φ ρvFr ρvsTo τ'
    ṽs ← exchange $ replicate len ṽM
    a ← io $ vecIMut ṽs
    m ← askL iCxtModeL
    return $ LocV m (Inr a)
  _         → todoCxt

------------
--- Comm ---
------------

commVal ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ≡ ρvFr) $ do
    commSendVal ρvFr ρvsTo ṽ
    chans ← list ^$ values ^$ getChannels ρvsTo
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    commRecvVal ρvFr ρvsTo τ
  else return unknownValDist

commSendVal ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → Val → IM Val ()
commSendVal ρvFr ρvsTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → do
      chans ← list ^$ values ^$ getChannels ρvsTo
      case bv of
        BoolV bool → do
          b ← elimClearBV bool
          eachOn chans $ \ chan → channelSendBool chan b
        NatV pr nat → do
          n ← elimClearNV nat
          eachOn chans $ \ chan → channelSendNat chan pr n
        IntV pr int → do
          z ← elimClearZV int
          eachOn chans $ \ chan → channelSendInt chan pr z
        _           → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      commSendVal ρvFr ρvsTo ṽ₁
      commSendVal ρvFr ρvsTo ṽ₂
    LocV _m (Inr a) → do
      commSendVal ρvFr ρvsTo $ KnownV $ BaseV $ NatV iprDefault $ ClearNV $ HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachWith (commSendVal ρvFr ρvsTo) ṽs
    _           → do
      pptraceM v
      todoCxt

commRecvVal ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → Type → IM Val Val
commRecvVal ρvFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ  → BaseV ^$ do
    chan ← getChannel ρvFr
    case bτ of
      𝔹T    → BoolV   ^$ ClearBV ^$ channelRecvBool chan
      ℕT pr → NatV pr ^$ ClearNV ^$ channelRecvNat  chan pr
      ℤT pr → IntV pr ^$ ClearZV ^$ channelRecvInt  chan pr
      _     → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← commRecvVal ρvFr ρvsTo τ₁
    ṽ₂ ← commRecvVal ρvFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  ArrT τ' → do
    _ :* len_nat ← elimNat *$ elimBase *$ elimKnown *$ commRecvVal ρvFr ρvsTo $ BaseT $ ℕT iprDefault
    len ← elimClearNV len_nat
    let ṽM = commRecvVal ρvFr ρvsTo τ'
    ṽs ← exchange $ replicate len ṽM
    a ← io $ vecIMut ṽs
    m ← askL iCxtModeL
    return $ LocV m (Inr a)
  _         → todoCxt

--------------
--- Reveal ---
--------------

revealVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Val → Type → IM Val Val
revealVal φ ρvsFr ρvTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    revealSendVal φ ρvsFr ρvTo ṽ
    chan ← getChannel ρvTo
    channelFlush chan
  if me ≡ ρvTo then do
    revealRecvVal φ ρvsFr ρvTo τ
  else return unknownValDist

revealSendVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Val → IM Val ()
revealSendVal φ ρvsFr ρvTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → case φ of
      GMWP → do
        gmw  ← getOrMkGmw ρvsFr
        chan ← getChannel ρvTo
        case bv of
          BoolV bool  → do
            eb ← elimEncBV ρvsFr bool
            b  ← elimGmwB eb
            gmwRevealSendGmwBool gmw chan b
          NatV pr nat → do
            en ← elimEncNV ρvsFr nat
            n  ← elimGmwN en
            gmwRevealSendGmwNat gmw chan pr n
          IntV pr int → do
            ez ← elimEncZV ρvsFr int
            z  ← elimGmwZ ez
            gmwRevealSendGmwInt gmw chan pr z
          _           → todoCxt
      _    → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      revealSendVal φ ρvsFr ρvTo ṽ₁
      revealSendVal φ ρvsFr ρvTo ṽ₂
    _           → todoCxt

revealRecvVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → PrinVal → Type → IM Val Val
revealRecvVal φ ρvsFr ρvTo τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ case φ of
    GMWP → do
      chans ← list ^$ values ^$ getChannels ρvsFr
      case bτ of
        𝔹T    → BoolV   ^$ ClearBV ^$ gmwRevealRecvBool chans
        ℕT pr → NatV pr ^$ ClearNV ^$ gmwRevealRecvNat chans pr
        ℤT pr → IntV pr ^$ ClearZV ^$ gmwRevealRecvInt chans pr
        _     → todoCxt
    _    → todoCxt
  τ₁ :×: τ₂ → do
      ṽ₁ ← revealRecvVal φ ρvsFr ρvTo τ₁
      ṽ₂ ← revealRecvVal φ ρvsFr ρvTo τ₂
      return $ ProdV ṽ₁ ṽ₂
  _ → todoCxt
