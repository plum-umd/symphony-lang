module Symphony.Dynamic.Par.GMW ( module Symphony.Dynamic.Par.GMW ) where

import Symphony.Prelude
import qualified Prelude as HS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CSize(..), CBool(..))
import Foreign.Marshal.Array (withArrayLen)
import Foreign.Marshal.Utils (toBool, fromBool)

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Prg
import Symphony.Dynamic.Par.Channel

import Symphony.Dynamic.Par.GMW.Types as Symphony.Dynamic.Par.GMW

-- GMW Protocol

foreign import ccall unsafe "gmw_protocol_new" gmw_protocol_new ∷ CSize → Ptr (Ptr CChannel) → CSize → IO (Ptr CGmw)

gmwProtocolNew ∷ (Monad m, MonadIO m) ⇒ PrinVal → (PrinVal ⇰ Channel) → m Gmw
gmwProtocolNew me chans = io $
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  Gmw ^$ newForeignPtr gmw_protocol_drop *$ gmw_protocol_new cme cchans_ptr (HS.fromIntegral len_cchans)
  where cme    = HS.fromIntegral $ fromSome $ idsFr (keys chans) ⋕? me
        cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans

foreign import ccall unsafe "&gmw_protocol_drop" gmw_protocol_drop ∷ FinalizerPtr CGmw

-- GMW Boolean Shares

foreign import ccall unsafe "gmw_bool_new" gmw_bool_new ∷ Ptr CGmw → CBool → IO (Ptr CGmwBool)

gmwBoolNew ∷ (Monad m, MonadIO m) ⇒ Gmw → 𝔹 → m GmwBool
gmwBoolNew gmw share = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_drop *$ gmw_bool_new cgmw_ptr cshare
  where cgmw   = unGmw gmw
        cshare = fromBool share

foreign import ccall unsafe "gmw_bool_constant" gmw_bool_constant ∷ Ptr CGmw → CBool → IO (Ptr CGmwBool)

gmwBoolConstant ∷ (Monad m, MonadIO m) ⇒ Gmw → 𝔹 → m GmwBool
gmwBoolConstant gmw value = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_drop *$ gmw_bool_constant cgmw_ptr cvalue
  where cgmw   = unGmw gmw
        cvalue = fromBool value

foreign import ccall unsafe "gmw_bool_and" gmw_bool_and ∷ Ptr CGmw → Ptr CGmwBool → Ptr CGmwBool → IO (Ptr CGmwBool)

gmwBoolAnd ∷ (Monad m, MonadIO m) ⇒ Gmw → GmwBool → GmwBool → m GmwBool
gmwBoolAnd gmw inp₁ inp₂ = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  withForeignPtr cinp₁ $ \ cinp₁_ptr →
  withForeignPtr cinp₂ $ \ cinp₂_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_drop *$ gmw_bool_and cgmw_ptr cinp₁_ptr cinp₂_ptr
  where cgmw  = unGmw gmw
        cinp₁ = unGmwBool inp₁
        cinp₂ = unGmwBool inp₂

foreign import ccall unsafe "gmw_bool_reify" gmw_bool_reify ∷ Ptr CGmw → Ptr CGmwBool → IO CBool

gmwBoolReify ∷ (Monad m, MonadIO m) ⇒ Gmw → GmwBool → m 𝔹
gmwBoolReify gmw share = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  withForeignPtr cshare $ \ cshare_ptr →
  toBool ^$ gmw_bool_reify cgmw_ptr cshare_ptr
  where cgmw   = unGmw gmw
        cshare = unGmwBool share

foreign import ccall unsafe "&gmw_bool_drop" gmw_bool_drop ∷ FinalizerPtr CGmwBool

-- GMW Utilities

foreign import ccall unsafe "gmw_share_send_bool" gmw_share_send_bool ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CBool → IO ()

gmwShareSendBool ∷ (Monad m, MonadIO m) ⇒ Prg → (PrinVal ⇰ Channel) → 𝔹 → m ()
gmwShareSendBool prg chans input = io $
  withForeignPtr cprg $ \ cprg_ptr →
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  gmw_share_send_bool cprg_ptr cchans_ptr (HS.fromIntegral len_cchans) cinput
  where cprg   = unPrg prg
        cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans
        cinput = fromBool input

foreign import ccall unsafe "gmw_share_recv_bool" gmw_share_recv_bool ∷ Ptr CChannel → IO CBool

gmwShareRecvBool ∷ (Monad m, MonadIO m) ⇒ Channel → m 𝔹
gmwShareRecvBool chan = io $
  withForeignPtr cchan $ \ cchan_ptr →
  toBool ^$ gmw_share_recv_bool cchan_ptr
  where cchan = unChannel chan

foreign import ccall unsafe "gmw_reveal_send_bool" gmw_reveal_send_bool ∷ Ptr CChannel → CBool → IO ()

gmwRevealSendBool ∷ (Monad m, MonadIO m) ⇒ Channel → 𝔹 → m ()
gmwRevealSendBool chan output = io $
  withForeignPtr cchan $ \ cchan_ptr →
  gmw_reveal_send_bool cchan_ptr coutput
  where cchan   = unChannel chan
        coutput = fromBool output

foreign import ccall unsafe "gmw_reveal_recv_bool" gmw_reveal_recv_bool ∷ Ptr (Ptr CChannel) → CSize → IO CBool

gmwRevealRecvBool ∷ (Monad m, MonadIO m) ⇒ (PrinVal ⇰ Channel) → m 𝔹
gmwRevealRecvBool chans = io $
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  toBool ^$ gmw_reveal_recv_bool cchans_ptr (HS.fromIntegral len_cchans)
  where cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans

-- Convenience

gmwShareRecvGmwBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → m GmwBool
gmwShareRecvGmwBool gmw chan = do
  b ← gmwShareRecvBool chan
  gmwBoolNew gmw b

gmwRevealSendGmwBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → GmwBool → m ()
gmwRevealSendGmwBool gmw chan share = do
  b ← gmwBoolReify gmw share
  gmwRevealSendBool chan b
