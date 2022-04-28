module Symphony.Dynamic.Par.Channel ( module Symphony.Dynamic.Par.Channel ) where

import Symphony.Prelude

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc

import Symphony.Lang.Syntax

import qualified Prelude as HS
import qualified Data.Word as W
import qualified Data.Text as T

import Symphony.Dynamic.Par.Channel.Types as Symphony.Dynamic.Par.Channel

foreign import ccall unsafe "channel_new_local" channel_new_local ∷ IO (Ptr CChannel)

channelNewLocal ∷ IO Channel
channelNewLocal = io $ Channel ^$ newForeignPtr channel_drop *$ channel_new_local

foreign import ccall unsafe "channel_new_tcp_client" channel_new_tcp_client ∷ CAddr → CPort → IO (Ptr CChannel)

channelNewTcpClient ∷ (Monad m, MonadIO m) ⇒ Addr → Port → m Channel
channelNewTcpClient addr port = io $ Channel ^$ withCString hsaddr $ \ caddr → newForeignPtr channel_drop *$ channel_new_tcp_client caddr cport
  where hsaddr = T.unpack $ tohs addr
        cport  = CUShort $ tohs port

foreign import ccall unsafe "channel_new_tcp_server" channel_new_tcp_server ∷ CAddr → CPort → IO (Ptr CChannel)

channelNewTcpServer ∷ (Monad m, MonadIO m) ⇒ Addr → Port → m Channel
channelNewTcpServer addr port = io $ Channel ^$ withCString hsaddr $ \ caddr → newForeignPtr channel_drop *$ channel_new_tcp_server caddr cport
  where hsaddr = T.unpack $ tohs addr
        cport  = CUShort $ tohs port

foreign import ccall unsafe "&channel_drop" channel_drop ∷ FinalizerPtr CChannel

foreign import ccall unsafe "channel_send_all" channel_send_all ∷ Ptr CChannel → Ptr a → CSize → IO ()

channelSendAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → CSize → m ()
channelSendAll chan buf len = io $ withForeignPtr cchan $ \ chan_ptr → channel_send_all chan_ptr buf len
  where cchan = unChannel chan

channelSendStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → a → m ()
channelSendStorable chan v = io $ do
  alloca $ \ buf → do
    poke buf v
    channelSendAll chan buf len
  where len = CSize $ HS.fromIntegral $ sizeOf v

foreign import ccall unsafe "channel_recv_all" channel_recv_all ∷ Ptr CChannel → Ptr a → CSize → IO ()

channelRecvAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → CSize → m ()
channelRecvAll chan buf len = io $ withForeignPtr cchan $ \ chan_ptr → channel_recv_all chan_ptr buf len
  where cchan = unChannel chan

channelRecvStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → m a
channelRecvStorable chan = io $ do
  alloca $ \ buf → do
    channelRecvAll chan buf len
    peek buf
  where len = CSize $ HS.fromIntegral $ sizeOf (undefined ∷ a)

-- Convenience

channelSendBool ∷ (Monad m, MonadIO m) ⇒ Channel → 𝔹 → m ()
channelSendBool = channelSendStorable @𝔹

channelRecvBool ∷ (Monad m, MonadIO m) ⇒ Channel → m 𝔹
channelRecvBool = channelRecvStorable @𝔹

channelSendNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℕ → m ()
channelSendNat chan pr n = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → channelSendStorable @ℕ32 chan $ HS.fromIntegral n
  _                                 → undefined

channelRecvNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℕ
channelRecvNat chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → HS.fromIntegral ^$ channelRecvStorable @ℕ32 chan
  _                                 → undefined

channelSendInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℤ → m ()
channelSendInt chan pr n = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → channelSendStorable @ℤ32 chan $ HS.fromIntegral n
  _                                 → undefined

channelRecvInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℤ
channelRecvInt chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → HS.fromIntegral ^$ channelRecvStorable @ℤ32 chan
  _                                 → undefined
