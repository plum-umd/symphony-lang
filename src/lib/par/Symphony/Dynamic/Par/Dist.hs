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

shareVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
shareVal φ ρvsFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvFr) $ do
    chans ← list ^$ values ^$ getChannels ρvsTo
    shareSendVal φ ρvsFr chans
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    chans ← list ^$ values ^$ getChannels ρvsFr
    shareRecvVal φ chans ρvsTo τ
  else return unknownValDist

shareSendVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝐿 Channel → Val → IM Val ()
shareSendVal φ ρvsFr chansTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → case φ of
      GMWP → do
        prg   ← getPrg
        case bv of
          BoolV bool  → gmwShareSendBool prg chansTo    *$ elimClearBV bool
          NatV pr nat → gmwShareSendNat  prg chansTo pr *$ elimClearNV nat
          IntV pr int → gmwShareSendInt  prg chansTo pr *$ elimClearZV int
          _           → todoCxt
      _    → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      shareSendVal φ ρvFr chansTo ṽ₁
      shareSendVal φ ρvFr chansTo ṽ₂
    ListV ṽs → do -- PICKUP HERE
      commSendVal ρvsTo $ KnownV $ BaseV $ NatV iprDefault $ ClearNV $ count ṽs
      eachWith (shareSendVal φ ρvFr ρvsTo) ṽs
    LocV _m (Inr a) → do
      commSendVal ρvsTo $ KnownV $ BaseV $ NatV iprDefault $ ClearNV $ HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachWith (shareSendVal φ ρvFr ρvsTo) ṽs
    _           → todoCxt

shareRecvVal ∷ (STACK) ⇒ Prot → 𝐿 Channel → 𝑃 PrinVal → Type → IM Val Val
shareRecvVal φ chansFr ρvsTo τ = KnownV ^$ case τ of
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
    _ :* len_nat ← elimNat *$ elimBase *$ elimKnown *$ commRecvVal ρvFr $ BaseT $ ℕT iprDefault
    len ← elimClearNV len_nat
    let ṽM = shareRecvVal φ ρvFr ρvsTo τ'
    ṽs ← list ^$ exchange $ replicate len ṽM
    return $ ListV ṽs
  ArrT τ' → do
    _ :* len_nat ← elimNat *$ elimBase *$ elimKnown *$ commRecvVal ρvFr $ BaseT $ ℕT iprDefault
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

commVal ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvsFr ρvsTo ṽ τ = do
  me   ← askL iCxtMeL
  ρvFr ← nominate ρvsFr
  when (me ≡ ρvFr) $ do
    chans ← list ^$ values ^$ getChannels ρvsTo
    commSendVal chans ṽ
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    chan ← getChannel ρvFr
    commRecvVal chan τ
  else return unknownValDist

commSendVal ∷ (STACK) ⇒ 𝐿 Channel → Val → IM Val ()
commSendVal chansTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → do
      case bv of
        BoolV bool → do
          b ← elimClearBV bool
          eachOn chansTo $ \ chanTo → channelSendBool chanTo b
        NatV pr nat → do
          n ← elimClearNV nat
          eachOn chansTo $ \ chanTo → channelSendNat chanTo pr n
        IntV pr int → do
          z ← elimClearZV int
          eachOn chansTo $ \ chanTo → channelSendInt chanTo pr z
        _           → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      commSendVal chansTo ṽ₁
      commSendVal chansTo ṽ₂
    LocV _m (Inr a) → do
      let length = length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (commSendVal chansTo) ṽs
    _           → do
      pptraceM v
      todoCxt

commRecvVal ∷ (STACK) ⇒ Channel → Type → IM Val Val
commRecvVal chanFr τ = KnownV ^$ case τ of
  BaseT bτ  → BaseV ^$ do
    case bτ of
      𝔹T    → BoolV   ^$ ClearBV ^$ channelRecvBool chanFr
      ℕT pr → NatV pr ^$ ClearNV ^$ channelRecvNat  chanFr pr
      ℤT pr → IntV pr ^$ ClearZV ^$ channelRecvInt  chanFr pr
      _     → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← commRecvVal chanFr τ₁
    ṽ₂ ← commRecvVal chanFr τ₂
    return $ ProdV ṽ₁ ṽ₂
  ArrT τ' → do
    length ← channelRecvNat chanFr iprDefault
    let ṽM = commRecvVal chanFr τ'
    ṽs ← exchange $ replicate length ṽM
    a ← io $ vecIMut ṽs
    m ← askL iCxtModeL
    return $ LocV m (Inr a)
  _         → todoCxt

--------------
--- Reveal ---
--------------

revealVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
revealVal φ ρvsFr ρvsTo ṽ τ = do
  me ← askL iCxtMeL
  when (me ∈ ρvsFr) $ do
    chans ← list ^$ values ^$ getChannels ρvsTo
    revealSendVal φ ρvsFr chans ṽ
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    chans ← list ^$ values ^$ getChannels ρvsFr
    revealRecvVal φ chans τ
  else return unknownValDist

revealSendVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝐿 Channel → Val → IM Val ()
revealSendVal φ ρvsFr chansTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → case φ of
      GMWP → do
        gmw  ← getOrMkGmw ρvsFr
        case bv of
          BoolV bool  → do
            b ← elimGmwB *$ elimEncBV ρvsFr bool
            eachOn chansTo $ \ chanTo → gmwRevealSendGmwBool gmw chanTo b
          NatV pr nat → do
            n  ← elimGmwN *$ elimEncNV ρvsFr nat
            eachOn chansTo $ \ chanTo → gmwRevealSendGmwNat gmw chanTo pr n
          IntV pr int → do
            z  ← elimGmwZ *$ elimEncZV ρvsFr int
            eachOn chansTo $ \ chanTo → gmwRevealSendGmwInt gmw chanTo pr z
          _           → todoCxt
      _    → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      revealSendVal φ ρvsFr chansTo ṽ₁
      revealSendVal φ ρvsFr chansTo ṽ₂
    LocV _m (Inr a) → do
      let length = length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (revealSendVal φ ρvsFr chansTo) ṽs
    _           → todoCxt

revealRecvVal ∷ (STACK) ⇒ Prot → 𝐿 Channel → Type → IM Val Val
revealRecvVal φ chansFr τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ case φ of
    GMWP → do
      case bτ of
        𝔹T    → BoolV   ^$ ClearBV ^$ gmwRevealRecvBool chansFr
        ℕT pr → NatV pr ^$ ClearNV ^$ gmwRevealRecvNat  chansFr pr
        ℤT pr → IntV pr ^$ ClearZV ^$ gmwRevealRecvInt  chansFr pr
        _     → todoCxt
    _    → todoCxt
  τ₁ :×: τ₂ → do
      ṽ₁ ← revealRecvVal φ chansFr τ₁
      ṽ₂ ← revealRecvVal φ chansFr τ₂
      return $ ProdV ṽ₁ ṽ₂
  ArrT τ' → do
    length :& _ ← mapMOn chansFr $ \ chanFr → channelRecvNat chanFr iprDefault
    let ṽM = revealRecvVal chansFr τ'
    ṽs ← exchange $ replicate length ṽM
    a ← io $ vecIMut ṽs
    m ← askL iCxtModeL
    return $ LocV m (Inr a)
  _ → todoCxt
