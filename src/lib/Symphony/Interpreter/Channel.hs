module Symphony.Interpreter.Channel where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Interpreter.Types

import Symphony.Interpreter.Error

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.C.Types

import qualified Prelude as HS
import qualified Data.Text as T
import qualified Data.ByteString as BS

type CPort = CUShort

cAddress ∷ 𝕊 → HS.String
cAddress = T.unpack ∘ tohs

cPort ∷ ℕ16 → CPort
cPort = CUShort ∘ tohs

cSize ∷ ℕ64 → CSize
cSize = CSize ∘ tohs

foreign import ccall unsafe "symphony/tcp_channel.h tcp_channel_create_client" tcp_channel_create_client ∷ CString → CPort → IO (Ptr ChannelStruct)
foreign import ccall unsafe "symphony/tcp_channel.h tcp_channel_create_server" tcp_channel_create_server ∷ CPort → IO (Ptr ChannelStruct)
foreign import ccall unsafe "symphony/channel.h &channel_destroy" channel_destroy ∷ FinalizerPtr ChannelStruct

foreign import ccall unsafe "symphony/channel.h send_all" send_all ∷ Ptr ChannelStruct → Ptr a → CSize → IO ()
foreign import ccall unsafe "symphony/channel.h recv_all" recv_all ∷ Ptr ChannelStruct → Ptr a → CSize → IO ()
foreign import ccall unsafe "symphony/channel.h flush" flush ∷ Ptr ChannelStruct → IO ()

tcpChannelCreateClient ∷ (Monad m, MonadIO m) ⇒ 𝕊 → ℕ16 → m Channel
tcpChannelCreateClient address port = io $ withCString (cAddress address) $ \ addr → newForeignPtr channel_destroy *$ tcp_channel_create_client addr (cPort port)

tcpChannelCreateServer ∷ (Monad m, MonadIO m) ⇒ ℕ16 → m Channel
tcpChannelCreateServer port = io $ newForeignPtr channel_destroy *$ tcp_channel_create_server (cPort port)

channelSendAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → ℕ64 → m ()
channelSendAll chan buf size = io $ withForeignPtr chan $ \ chan_ptr → send_all chan_ptr buf (cSize size)

channelRecvAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → ℕ64 → m ()
channelRecvAll chan buf size = io $ withForeignPtr chan $ \ chan_ptr → recv_all chan_ptr buf (cSize size)

channelFlush ∷ (Monad m, MonadIO m) ⇒ Channel → m ()
channelFlush chan = io $ withForeignPtr chan $ \ chan_ptr → flush chan_ptr

-- Convenience

channelSendStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → a → m ()
channelSendStorable chan v = io $ withForeignPtr chan $ \ chan_ptr →
  alloca $ \ buf → do
    poke buf v
    send_all chan_ptr buf size
  where size = CSize $ HS.fromIntegral $ sizeOf v

channelRecvStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → m a
channelRecvStorable chan = io $ withForeignPtr chan $ \ chan_ptr →
  alloca $ \ buf → do
    recv_all chan_ptr buf size
    peek buf
  where size = CSize $ HS.fromIntegral $ sizeOf (undefined ∷ a)
