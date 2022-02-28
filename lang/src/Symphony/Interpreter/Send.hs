module Symphony.Interpreter.Send where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Pretty()
import Symphony.Interpreter.Lens
import Symphony.Interpreter.Error
import Symphony.Interpreter.NetIO

import qualified Prelude as HS

----------------
--- Channels ---
----------------

getOrMkChannel ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → PrinVal → m NetIO
getOrMkChannel ρvMe ρvThem = do
  channels ← getL iStateChannelsL
  case channels ⋕? ρvThem of
    None → do
      ch ← netIOCreate ρvMe ρvThem False
      modifyL iStateChannelsL ((ρvThem ↦ ch) ⩌!)
      return ch
    Some ch → return ch

----------------------------
--- Send / Recv BaseVal ---
----------------------------

sendClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → PrinVal → ClearBaseVal → m ()
sendClearBaseVal ρvFr ρvTo bv = do
  ch ← getOrMkChannel ρvFr ρvTo
  case bv of
    BoolV b → io $ netIOSendStorable ch b
    NatV pr n → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → io $ netIOSendStorable @ℕ8  ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → io $ netIOSendStorable @ℕ16 ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ netIOSendStorable @ℕ32 ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → io $ netIOSendStorable @ℕ64 ch $ HS.fromIntegral n
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    IntV pr z → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → io $ netIOSendStorable @ℤ8  ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → io $ netIOSendStorable @ℤ16 ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ netIOSendStorable @ℤ32 ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → io $ netIOSendStorable @ℤ64 ch $ HS.fromIntegral z
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿

recvClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → PrinVal → BaseType → m ClearBaseVal
recvClearBaseVal ρvFr ρvTo bτ = do
  ch ← getOrMkChannel ρvTo ρvFr
  case bτ of
    𝔹T → do
      b ← io $ netIORecvStorable ch
      return $ BoolV b
    ℕT pr → do
      n ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → map HS.fromIntegral $ io $ netIORecvStorable @ℕ8 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → map HS.fromIntegral $ io $ netIORecvStorable @ℕ16 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → map HS.fromIntegral $ io $ netIORecvStorable @ℕ32 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → map HS.fromIntegral $ io $ netIORecvStorable @ℕ64 ch
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ NatV pr n
    ℤT pr → do
      z ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → map HS.fromIntegral $ io $ netIORecvStorable @ℤ8 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → map HS.fromIntegral $ io $ netIORecvStorable @ℤ16 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → map HS.fromIntegral $ io $ netIORecvStorable @ℤ32 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → map HS.fromIntegral $ io $ netIORecvStorable @ℤ64 ch
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ IntV pr z
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿

-------------------
--- Convenience ---
-------------------

commClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m ClearBaseVal
commClearBaseVal ρvFr ρvsTo bvcorbτ = do
  ρvMe ← fromSomeCxt *$ askL iCxtMeL
  case bvcorbτ of
    Inl bvc → do
      when (ρvMe ≡ ρvFr) $ eachWith (\ ρvTo → sendClearBaseVal ρvFr ρvTo bvc) ρvsRecv
      when (ρvMe ∈ ρvsRecv) $ do
        bvc' ← recvClearBaseVal ρvFr ρvMe $ typeFrClearBaseVal bvc
        assertCxt (bvc ≡ bvc')
      return bvc
    Inr bτ → recvClearBaseVal ρvFr ρvMe bτ
  where ρvsRecv = ρvsTo ∖ (single𝑃 ρvFr)
