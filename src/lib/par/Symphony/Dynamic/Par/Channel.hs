module Symphony.Dynamic.Par.Channel ( module Symphony.Dynamic.Par.Channel ) where

import Symphony.Prelude

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc

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

{-
tohsPort ∷ ℕ16 → CPort
tohsPort = CUShort ∘ tohs

tohsAddr ∷ 𝕊 → HS.String
tohsAddr = T.unpack ∘ tohs

tohsCSize ∷ ℕ64 → CSize
tohsCSize = CSize ∘ tohs


foreign import ccall unsafe "symphony/tcp_channel.h tcp_channel_create_server" tcp_channel_create_server ∷ CPort → IO (Ptr ())


foreign import ccall unsafe "symphony/channel.h send_all" send_all ∷ Ptr () → Ptr a → CSize → IO ()
foreign import ccall unsafe "symphony/channel.h recv_all" recv_all ∷ Ptr () → Ptr a → CSize → IO ()
foreign import ccall unsafe "symphony/channel.h flush" flush ∷ Ptr () → IO ()

-}

channelSendAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → ℕ64 → m ()
channelSendAll chan buf size = undefined --io $ withForeignPtr chan $ \ chan_ptr → send_all chan_ptr buf (tohsCSize size)

channelRecvAll ∷ (Monad m, MonadIO m) ⇒ Channel → Ptr a → ℕ64 → m ()
channelRecvAll chan buf size = undefined --io $ withForeignPtr chan $ \ chan_ptr → recv_all chan_ptr buf (tohsCSize size)

channelFlush ∷ (Monad m, MonadIO m) ⇒ Channel → m ()
channelFlush chan = undefined --io $ withForeignPtr chan $ \ chan_ptr → flush chan_ptr

-- Convenience

channelSendStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → a → m ()
channelSendStorable chan v = undefined {-io $ withForeignPtr chan $ \ chan_ptr →
  alloca $ \ buf → do
    poke buf v
    send_all chan_ptr buf size
  where size = CSize $ HS.fromIntegral $ sizeOf v -}

channelRecvStorable ∷ forall a m . (Monad m, MonadIO m, Storable a) ⇒ Channel → m a
channelRecvStorable chan = undefined {-io $ withForeignPtr chan $ \ chan_ptr →
  alloca $ \ buf → do
    recv_all chan_ptr buf size
    peek buf
  where size = CSize $ HS.fromIntegral $ sizeOf (undefined ∷ a) -}
