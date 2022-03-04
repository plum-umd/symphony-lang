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

sendClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ Channel → ClearBaseVal → m ()
sendClearBaseVal chanTo = \case
    BoolV b → channelSendStorable chanTo b
    NatV pr n → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → channelSendStorable @ℕ8  chanTo $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → channelSendStorable @ℕ16 chanTo $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → channelSendStorable @ℕ32 chanTo $ HS.fromIntegral n
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → channelSendStorable @ℕ64 chanTo $ HS.fromIntegral n
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    IntV pr z → case pr of
      FixedIPr wPr dPr | wPr + dPr ≡ 8  → channelSendStorable @ℤ8  chanTo $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 16 → channelSendStorable @ℤ16 chanTo $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 32 → channelSendStorable @ℤ32 chanTo $ HS.fromIntegral z
      FixedIPr wPr dPr | wPr + dPr ≡ 64 → channelSendStorable @ℤ64 chanTo $ HS.fromIntegral z
      _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿

recvClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ Channel → BaseType → m ClearBaseVal
recvClearBaseVal chanFr = \case
    𝔹T → do
      b ← channelRecvStorable chanFr
      return $ BoolV b
    ℕT pr → do
      n ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → HS.fromIntegral ^$ channelRecvStorable @ℕ8 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → HS.fromIntegral ^$ channelRecvStorable @ℕ16 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → HS.fromIntegral ^$ channelRecvStorable @ℕ32 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → HS.fromIntegral ^$ channelRecvStorable @ℕ64 chanFr
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ NatV pr n
    ℤT pr → do
      z ← case pr of
            FixedIPr wPr dPr | wPr + dPr ≡ 8  → HS.fromIntegral ^$ channelRecvStorable @ℤ8 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 16 → HS.fromIntegral ^$ channelRecvStorable @ℤ16 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 32 → HS.fromIntegral ^$ channelRecvStorable @ℤ32 chanFr
            FixedIPr wPr dPr | wPr + dPr ≡ 64 → HS.fromIntegral ^$ channelRecvStorable @ℤ64 chanFr
            _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
      return $ IntV pr z
    _ → throwIErrorCxt NotImplementedIError "TODO" empty𝐿
