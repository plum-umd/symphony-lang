module Symphony.Dynamic.Par.Send where
{-
import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Channel

import qualified Prelude as HS
import qualified Data.Text as T

addressOf ∷ (Monad m) ⇒ PrinVal → m 𝕊
addressOf _ = return "127.0.0.1"

portOf ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → PrinVal → m ℕ16
portOf ρ₁ ρ₂ = do
  scope ← askL iCxtPrinScopeL
  let n = count scope
  let ids = idsFr scope
  id₁   ← fromSomeCxt $ ids ⋕? ρ₁
  id₂   ← fromSomeCxt $ ids ⋕? ρ₂
  let gauss  = ((id₁ + 1) × (id₁ + 2)) `HS.div` 2
  let offset = n × id₁ + id₂ - gauss
  return $ HS.fromIntegral $ basePort + offset
  where basePort = 12345

----------------
--- Channels ---
----------------

mkChannel ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ PrinVal → m Channel
mkChannel them = do
  me ← askL iCxtMeL
  let iAmClient = them < me
  if iAmClient then do
    addr ← addressOf them
    port ← portOf them me
    tcpChannelCreateClient addr port
  else do
    port ← portOf me them
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

getOrMkChannels ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ 𝑃 PrinVal → m (PrinVal ⇰ Channel)
getOrMkChannels them = map dict $ mapM (\ ρv → map ((↦) ρv) (getOrMkChannel ρv)) $ iter them

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
-}
