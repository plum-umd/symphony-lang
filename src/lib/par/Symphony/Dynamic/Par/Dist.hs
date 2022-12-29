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
  when (me ∈ ρvsFr) $ do
    chans ← list ^$ values ^$ getChannels ρvsTo
    shareSendVal φ ρvsFr chans ṽ
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
      RepP → case bv of
        BoolV (ClearBV b)    → eachOn chansTo $ \ chanTo → channelSendBool chanTo b
        BoolV (EncBV ρvs eb) → do
          encCheck ρvsFr ρvs
          b ← elimRepB eb
          eachOn chansTo $ \ chanTo → channelSendBool chanTo b
        NatV pr (ClearNV n)    → eachOn chansTo $ \ chanTo → channelSendNat chanTo pr n
        NatV pr (EncNV ρvs en) → do
          encCheck ρvsFr ρvs
          n ← elimRepN en
          eachOn chansTo $ \ chanTo → channelSendNat chanTo pr n
        IntV pr (ClearZV z)    → eachOn chansTo $ \ chanTo → channelSendInt chanTo pr z
        IntV pr (EncZV ρvs ez) → do
            encCheck ρvsFr ρvs
            z ← elimRepZ ez
            eachOn chansTo $ \ chanTo → channelSendInt chanTo pr z
        _ → todoCxt
      GmwP → do
        prg   ← getPrg
        case bv of
          BoolV (ClearBV b)    → gmwShareSendBool prg chansTo b
          BoolV (EncBV ρvs eb) → do
            encCheck ρvsFr ρvs
            gmw ← getOrMkGmw ρvsFr
            b ← elimGmwB eb
            gmwReshareSendBool gmw prg chansTo b
          NatV pr (ClearNV n)    → gmwShareSendNat prg chansTo pr n
          NatV pr (EncNV ρvs en) → do
            encCheck ρvsFr ρvs
            gmw ← getOrMkGmw ρvsFr
            n ← elimGmwN en
            gmwReshareSendNat gmw prg chansTo pr n
          IntV pr (ClearZV z) → gmwShareSendInt prg chansTo pr z
          IntV pr (EncZV ρvs ez) → do
            encCheck ρvsFr ρvs
            gmw ← getOrMkGmw ρvsFr
            z ← elimGmwZ ez
            gmwReshareSendInt gmw prg chansTo pr z
          _           → todoCxt
      _    → todoCxt
    ProdV ṽ₁ ṽ₂ → do
      shareSendVal φ ρvsFr chansTo ṽ₁
      shareSendVal φ ρvsFr chansTo ṽ₂
    ListV ṽs → do
      let length = count ṽs
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (shareSendVal φ ρvsFr chansTo) ṽs
    LocV _m (Inr a) → do
      let length = HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (shareSendVal φ ρvsFr chansTo) ṽs
    _           → todoCxt

shareRecvVal ∷ (STACK) ⇒ Prot → 𝐿 Channel → 𝑃 PrinVal → Type → IM Val Val
shareRecvVal φ chansFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ case φ of
    RepP → case bτ of
      𝔹T    → BoolV   ^$ EncBV ρvsTo ^$ RepB ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvBool chanFr
      ℕT pr → NatV pr ^$ EncNV ρvsTo ^$ RepN ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr pr
      ℤT pr → IntV pr ^$ EncZV ρvsTo ^$ RepZ ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvInt chanFr pr
      _     → todoCxt
    GmwP → do
      gmw  ← getOrMkGmw ρvsTo
      case bτ of
        𝔹T    → BoolV   ^$ EncBV ρvsTo ^$ GmwB ^$ case chansFr of
                                                    chanFr :& Nil → gmwShareRecvGmwBool gmw chanFr
                                                    _             → gmwReshareRecvGmwBool gmw chansFr
        ℕT pr → NatV pr ^$ EncNV ρvsTo ^$ GmwN ^$ case chansFr of
                                                    chanFr :& Nil → gmwShareRecvGmwNat gmw chanFr pr
                                                    _             → gmwReshareRecvGmwNat gmw chansFr pr
        ℤT pr → IntV pr ^$ EncZV ρvsTo ^$ GmwZ ^$ case chansFr of
                                                    chanFr :& Nil → gmwShareRecvGmwInt gmw chanFr pr
                                                    _             → gmwReshareRecvGmwInt gmw chansFr pr
        _     → todoCxt
    _    → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← shareRecvVal φ chansFr ρvsTo τ₁
    ṽ₂ ← shareRecvVal φ chansFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  ListT τ' → do
    length ← access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr iprDefault
    let ṽM = shareRecvVal φ chansFr ρvsTo τ'
    ṽs ← list ^$ exchange $ replicate length ṽM
    return $ ListV ṽs
  ArrT τ' → do
    length ← access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr iprDefault
    let ṽM = shareRecvVal φ chansFr ρvsTo τ'
    ṽs ← exchange $ replicate length ṽM
    a ← io $ vecIMut ṽs
    return $ LocV (AddTop ρvsTo) (Inr a)
  _         → todoCxt

------------
--- Comm ---
------------

commVal ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Val → Type → IM Val Val
commVal ρvsFr ρvsTo ṽ τ = do
  me   ← askL iCxtMeL
  let nominate ρvs = fromSomeCxt $ choose𝑃 ρvs
  ρvFr ← nominate ρvsFr
  when (me ≡ ρvFr) $ do
    chans ← list ^$ values ^$ getChannels ρvsTo
    commSendVal chans ṽ
    eachWith channelFlush chans
  if me ∈ ρvsTo then do
    chan ← getChannel ρvFr
    commRecvVal chan ρvsTo τ
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
      let length = HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (commSendVal chansTo) ṽs
    _           → do
      pptraceM v
      todoCxt

commRecvVal ∷ (STACK) ⇒ Channel → 𝑃 PrinVal → Type → IM Val Val
commRecvVal chanFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ  → BaseV ^$ do
    case bτ of
      𝔹T    → BoolV   ^$ ClearBV ^$ channelRecvBool chanFr
      ℕT pr → NatV pr ^$ ClearNV ^$ channelRecvNat  chanFr pr
      ℤT pr → IntV pr ^$ ClearZV ^$ channelRecvInt  chanFr pr
      _     → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← commRecvVal chanFr ρvsTo τ₁
    ṽ₂ ← commRecvVal chanFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  ArrT τ' → do
    length ← channelRecvNat chanFr iprDefault
    let ṽM = commRecvVal chanFr ρvsTo τ'
    ṽs ← exchange $ replicate length ṽM
    a ← io $ vecIMut ṽs
    return $ LocV (AddTop ρvsTo) (Inr a)
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
    revealRecvVal φ chans ρvsTo τ
  else return unknownValDist

revealSendVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → 𝐿 Channel → Val → IM Val ()
revealSendVal φ ρvsFr chansTo ṽ = do
  v ← elimKnown ṽ
  case v of
    BaseV bv → case φ of
      RepP → case bv of
        BulV       → return ()
        BoolV bool → do
          b ← elimRepB *$ elimEncBV ρvsFr bool
          eachOn chansTo $ \ chanTo → channelSendBool chanTo b
        NatV pr nat → do
          n ← elimRepN *$ elimEncNV ρvsFr nat
          eachOn chansTo $ \ chanTo → channelSendNat chanTo pr n
        IntV pr int → do
          z ← elimRepZ *$ elimEncZV ρvsFr int
          eachOn chansTo $ \ chanTo → channelSendInt chanTo pr z
        _ → todoCxt
      GmwP → do
        gmw  ← getOrMkGmw ρvsFr
        case bv of
          BulV        → return ()
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
    SumV b ṽ₁ ṽ₂ → do
      revealSendVal φ ρvsFr chansTo $ KnownV $ BaseV $ BoolV b
      revealSendVal φ ρvsFr chansTo ṽ₁
      revealSendVal φ ρvsFr chansTo ṽ₂
    ListV ṽs → do
      let length = count ṽs
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (revealSendVal φ ρvsFr chansTo) ṽs
    LocV _m (Inr a) → do
      let length = HS.fromIntegral $ length𝕍Mut a
      ṽs ← io $ values𝕍Mut a
      eachOn chansTo $ \ chanTo → channelSendNat chanTo iprDefault length
      eachWith (revealSendVal φ ρvsFr chansTo) ṽs
    _           → do { pptraceM v; todoCxt }

revealRecvVal ∷ (STACK) ⇒ Prot → 𝐿 Channel → 𝑃 PrinVal → Type → IM Val Val
revealRecvVal φ chansFr ρvsTo τ = KnownV ^$ case τ of
  BaseT bτ → BaseV ^$ case φ of
    RepP → case bτ of
      UnitT → return BulV
      𝔹T    → BoolV   ^$ ClearBV ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvBool chanFr
      ℕT pr → NatV pr ^$ ClearNV ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr pr
      ℤT pr → IntV pr ^$ ClearZV ^$ access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvInt chanFr pr
      _     → todoCxt
    GmwP → do
      case bτ of
        UnitT → return BulV
        𝔹T    → BoolV   ^$ ClearBV ^$ gmwRevealRecvBool chansFr
        ℕT pr → NatV pr ^$ ClearNV ^$ gmwRevealRecvNat  chansFr pr
        ℤT pr → IntV pr ^$ ClearZV ^$ gmwRevealRecvInt  chansFr pr
        _     → todoCxt
    _    → todoCxt
  τ₁ :×: τ₂ → do
    ṽ₁ ← revealRecvVal φ chansFr ρvsTo τ₁
    ṽ₂ ← revealRecvVal φ chansFr ρvsTo τ₂
    return $ ProdV ṽ₁ ṽ₂
  τ₁ :+: τ₂ → do
    b  ← elimBool *$ elimBase *$ elimKnown *$ revealRecvVal φ chansFr ρvsTo $ BaseT 𝔹T
    ṽ₁ ← revealRecvVal φ chansFr ρvsTo τ₁
    ṽ₂ ← revealRecvVal φ chansFr ρvsTo τ₂
    return $ SumV b ṽ₁ ṽ₂
  ListT τ' → do
    length ← access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr iprDefault
    let ṽM = revealRecvVal φ chansFr ρvsTo τ'
    ṽs ← exchange $ replicate length ṽM
    return $ ListV $ list ṽs
  ArrT τ' → do
    length ← access fstL ^$ fromSomeCxt *$ view consL ^$ mapMOn chansFr $ \ chanFr → channelRecvNat chanFr iprDefault
    let ṽM = revealRecvVal φ chansFr ρvsTo τ'
    ṽs ← exchange $ replicate length ṽM
    a ← io $ vecIMut ṽs
    return $ LocV (AddTop ρvsTo) (Inr a)
  _ → todoCxt
