module Symphony.Interpreter.Send where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Pretty()
import Symphony.Interpreter.Lens
import Symphony.Interpreter.Error
import Symphony.Interpreter.Channel

import qualified Prelude as HS
import qualified Data.Text as T

addressOf ∷ (Monad m) ⇒ PrinVal → m 𝕊
addressOf _ = return "127.0.0.1"

portOf ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → m ℕ16
portOf ρ = do
  scope ← askL iCxtPrinScopeL
  let ports = map ((+) basePort) $ idsFr scope
  port ← fromSomeCxt $ ports ⋕? ρ
  return $ HS.fromIntegral port
  where basePort = 12345

----------------
--- Channels ---
----------------

mkChannel ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → m Channel
mkChannel them = do
  me ← fromSomeCxt *$ askL iCxtMeL
  let iAmClient = them < me
  if iAmClient then do
    addr ← addressOf them
    port ← portOf them
    tcpChannelCreateClient addr port
  else do
    port ← portOf me
    tcpChannelCreateServer port

getOrMkChannel ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → m Channel
getOrMkChannel them = do
  channels ← getL iStateChannelsL
  case channels ⋕? them of
    None → do
      chan ← mkChannel them
      modifyL iStateChannelsL ((them ↦ chan) ⩌!)
      return chan
    Some chan → return chan

----------------------------
--- Send / Recv BaseVal ---
----------------------------

sendClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → ClearBaseVal → m ()
sendClearBaseVal to bv = do
  ch ← getOrMkChannel to
  case bv of
    BoolV b → io $ channelSendStorable ch b
    NatV pr n → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → io $ channelSendStorable @ℕ8  ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → io $ channelSendStorable @ℕ16 ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ channelSendStorable @ℕ32 ch $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → io $ channelSendStorable @ℕ64 ch $ HS.fromIntegral n
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    IntV pr z → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → io $ channelSendStorable @ℤ8  ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → io $ channelSendStorable @ℤ16 ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ channelSendStorable @ℤ32 ch $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → io $ channelSendStorable @ℤ64 ch $ HS.fromIntegral z
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿

recvClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → BaseType → m ClearBaseVal
recvClearBaseVal fr bτ = do
  ch ← getOrMkChannel fr
  case bτ of
    𝔹T → do
      b ← io $ channelRecvStorable ch
      return $ BoolV b
    ℕT pr → do
      n ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → map HS.fromIntegral $ io $ channelRecvStorable @ℕ8 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → map HS.fromIntegral $ io $ channelRecvStorable @ℕ16 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → map HS.fromIntegral $ io $ channelRecvStorable @ℕ32 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → map HS.fromIntegral $ io $ channelRecvStorable @ℕ64 ch
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ NatV pr n
    ℤT pr → do
      z ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → map HS.fromIntegral $ io $ channelRecvStorable @ℤ8 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → map HS.fromIntegral $ io $ channelRecvStorable @ℤ16 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → map HS.fromIntegral $ io $ channelRecvStorable @ℤ32 ch
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → map HS.fromIntegral $ io $ channelRecvStorable @ℤ64 ch
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ IntV pr z
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
