module Symphony.Dynamic.Par.GMW ( module Symphony.Dynamic.Par.GMW ) where

import Symphony.Prelude
import qualified Prelude as HS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, ForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CSize(..), CBool(..), CUInt(..), CInt(..))
import Foreign.Marshal.Array (withArrayLen, withArray)
import Foreign.Marshal.Utils (toBool, fromBool)
import qualified Data.Text as T

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Prg
import Symphony.Dynamic.Par.Channel

import Symphony.Dynamic.Par.GMW.Types as Symphony.Dynamic.Par.GMW

-- Utilities, these should be moved to Prelude

unChans ∷ 𝐿 Channel → [ForeignPtr CChannel]
unChans chans = tohs $ list $ map unChannel $ iter chans

reflectPtr ∷ (a → IO (Ptr b)) → FinalizerPtr b → a → IO (ForeignPtr b)
reflectPtr reflect elim v = newForeignPtr elim *$ reflect v

unaryPtr ∷ (Ptr a → IO (Ptr b)) → FinalizerPtr b → ForeignPtr a → IO (ForeignPtr b)
unaryPtr op elim v =
  withForeignPtr v $ \ v →
  newForeignPtr elim *$ op v

binaryPtr ∷ (Ptr a → Ptr b → IO (Ptr c)) → FinalizerPtr c → ForeignPtr a → ForeignPtr b → IO (ForeignPtr c)
binaryPtr op elim v₁ v₂ =
  withForeignPtr v₁ $ \ v₁ →
  withForeignPtr v₂ $ \ v₂ →
  newForeignPtr elim *$ op v₁ v₂



reifyPtr ∷ (Ptr a → IO b) → ForeignPtr a → IO b
reifyPtr reify v =
  withForeignPtr v $ \ v →
  reify v

--------------------
--- GMW Protocol ---
--------------------

foreign import ccall unsafe "gmw_protocol_new" gmw_protocol_new ∷ CSize → Ptr CAddr → Ptr CPort → CSize → IO (Ptr CGmw)

gmwProtocolNew ∷ (Monad m, MonadIO m) ⇒ PrinVal → (PrinVal ⇰ (Addr ∧ Port)) → m Gmw
gmwProtocolNew me chans = io $
  withCStrings caddrs $ \ caddr_ptrs →
  withArrayLen caddr_ptrs $ \ len caddrs_ptr →
  withArray cports $ \ cports_ptr →
  Gmw ^$ newForeignPtr gmw_protocol_drop *$ gmw_protocol_new cme caddrs_ptr cports_ptr (HS.fromIntegral len)
  where cme    = HS.fromIntegral $ fromSome $ idsFr (keys chans) ⋕? me
        caddrs = lazyList𝐼 $ map (T.unpack ∘ fst ∘ snd) $ iter chans
        cports = tohs $ list $ map (HS.fromIntegral ∘ snd ∘ snd) $ iter chans

foreign import ccall unsafe "&gmw_protocol_drop" gmw_protocol_drop ∷ FinalizerPtr CGmw

withGmw ∷ Gmw → (Ptr CGmw → IO a) → IO a
withGmw gmw f = withForeignPtr cgmw f
  where cgmw = unGmw gmw

gmwReflect ∷ (Ptr CGmw → a → IO (Ptr b)) → FinalizerPtr b → Gmw → a → IO (ForeignPtr b)
gmwReflect reflect elim gmw v =
  withGmw gmw $ \ gmw →
  reflectPtr (reflect gmw) elim v

gmwUnary ∷ (Ptr CGmw → Ptr a → IO (Ptr b)) → FinalizerPtr b → Gmw → ForeignPtr a → IO (ForeignPtr b)
gmwUnary op elim gmw v =
  withGmw gmw $ \ gmw →
  unaryPtr (op gmw) elim v

gmwBinary ∷ (Ptr CGmw → Ptr a → Ptr b → IO (Ptr c)) → FinalizerPtr c → Gmw → ForeignPtr a → ForeignPtr b → IO (ForeignPtr c)
gmwBinary op elim gmw v₁ v₂ =
  withGmw gmw $ \ gmw →
  binaryPtr (op gmw) elim v₁ v₂

gmwReify ∷ (Ptr CGmw → Ptr a → IO b) → Gmw → ForeignPtr a → IO b
gmwReify reify gmw v =
  withGmw gmw $ \ gmw →
  reifyPtr (reify gmw) v

gmwShareSend ∷ (Ptr CPrg → Ptr (Ptr CChannel) → CSize → a → IO ()) → Prg → 𝐿 Channel → a → IO ()
gmwShareSend shareSend prg chans v =
  withForeignPtr (unPrg prg) $ \ prg →
  withForeignPtrs (unChans chans) $ \ chans →
  withArrayLen chans $ \ len buf →
  shareSend prg buf (HS.fromIntegral len) v

gmwShareRecv ∷ (Ptr CChannel → IO a) → Channel → IO a
gmwShareRecv shareRecv chan =
  withForeignPtr (unChannel chan) $ \ chan →
  shareRecv chan

gmwRevealSend ∷ (Ptr CChannel → a → IO ()) → Channel → a → IO ()
gmwRevealSend revealSend chan v =
  withForeignPtr (unChannel chan) $ \ chan →
  revealSend chan v

gmwRevealRecv ∷ (Ptr (Ptr CChannel) → CSize → IO a) → 𝐿 Channel → IO a
gmwRevealRecv revealRecv chans =
  withForeignPtrs (unChans chans) $ \ chans →
  withArrayLen chans $ \ len buf →
  revealRecv buf (HS.fromIntegral len)

----------------
--- GMW Bool ---
----------------

foreign import ccall unsafe "gmw_bool_new" gmw_bool_new ∷ Ptr CGmw → CBool → IO (Ptr CGmwBool)

gmwBoolNew ∷ (Monad m, MonadIO m) ⇒ Gmw → 𝔹 → m GmwBool
gmwBoolNew gmw share = io $ GmwBool ^$ gmwReflect gmw_bool_new gmw_bool_drop gmw $ fromBool share

foreign import ccall unsafe "gmw_bool_constant" gmw_bool_constant ∷ Ptr CGmw → CBool → IO (Ptr CGmwBool)

gmwBoolConstant ∷ (Monad m, MonadIO m) ⇒ Gmw → 𝔹 → m GmwBool
gmwBoolConstant gmw value = io $ GmwBool ^$ gmwReflect gmw_bool_constant gmw_bool_drop gmw $ fromBool value

foreign import ccall unsafe "gmw_bool_and" gmw_bool_and ∷ Ptr CGmw → Ptr CGmwBool → Ptr CGmwBool → IO (Ptr CGmwBool)

gmwBoolAnd ∷ (Monad m, MonadIO m) ⇒ Gmw → GmwBool → GmwBool → m GmwBool
gmwBoolAnd gmw v₁ v₂ = io $ GmwBool ^$ gmwBinary gmw_bool_and gmw_bool_drop gmw (unGmwBool v₁) (unGmwBool v₂)

foreign import ccall unsafe "gmw_bool_reify" gmw_bool_reify ∷ Ptr CGmw → Ptr CGmwBool → IO CBool

gmwBoolReify ∷ (Monad m, MonadIO m) ⇒ Gmw → GmwBool → m 𝔹
gmwBoolReify gmw share = io $ toBool ^$ gmwReify gmw_bool_reify gmw (unGmwBool share)

foreign import ccall unsafe "&gmw_bool_drop" gmw_bool_drop ∷ FinalizerPtr CGmwBool

-- Delegation --

foreign import ccall unsafe "gmw_share_send_bool" gmw_share_send_bool ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CBool → IO ()

gmwShareSendBool ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → 𝔹 → m ()
gmwShareSendBool prg chans input = io $ gmwShareSend gmw_share_send_bool prg chans $ fromBool input

foreign import ccall unsafe "gmw_share_recv_bool" gmw_share_recv_bool ∷ Ptr CChannel → IO CBool

gmwShareRecvBool ∷ (Monad m, MonadIO m) ⇒ Channel → m 𝔹
gmwShareRecvBool chan = io $ toBool ^$ gmwShareRecv gmw_share_recv_bool chan

foreign import ccall unsafe "gmw_reveal_send_bool" gmw_reveal_send_bool ∷ Ptr CChannel → CBool → IO ()

gmwRevealSendBool ∷ (Monad m, MonadIO m) ⇒ Channel → 𝔹 → m ()
gmwRevealSendBool chan output = io $ gmwRevealSend gmw_reveal_send_bool chan $ fromBool output

foreign import ccall unsafe "gmw_reveal_recv_bool" gmw_reveal_recv_bool ∷ Ptr (Ptr CChannel) → CSize → IO CBool

gmwRevealRecvBool ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → m 𝔹
gmwRevealRecvBool chans = io $ toBool ^$ gmwRevealRecv gmw_reveal_recv_bool chans

gmwShareRecvGmwBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → m GmwBool
gmwShareRecvGmwBool gmw chan = do
  b ← gmwShareRecvBool chan
  gmwBoolNew gmw b

gmwRevealSendGmwBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → GmwBool → m ()
gmwRevealSendGmwBool gmw chan share = do
  b ← gmwBoolReify gmw share
  gmwRevealSendBool chan b

----------------------------------
--- GMW Natural (Unsigned Int) ---
----------------------------------

foreign import ccall unsafe "gmw_nat32_new" gmw_nat32_new ∷ Ptr CGmw → CUInt → IO (Ptr CGmwNat)

gmwNatNew ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → ℕ → m GmwNat
gmwNatNew gmw pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ GmwNat ^$ gmwReflect gmw_nat32_new gmw_nat_drop gmw $ HS.fromIntegral share
  _                                → undefined

foreign import ccall unsafe "gmw_nat32_constant" gmw_nat32_constant ∷ Ptr CGmw → CUInt → IO (Ptr CGmwNat)

gmwNatConstant ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → ℕ → m GmwNat
gmwNatConstant gmw pr value = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ GmwNat ^$ gmwReflect gmw_nat32_constant gmw_nat_drop gmw $ HS.fromIntegral value
  _                                → undefined

foreign import ccall unsafe "gmw_nat32_reify" gmw_nat32_reify ∷ Ptr CGmw → Ptr CGmwNat → IO CUInt

gmwNatReify ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → GmwNat → m ℕ
gmwNatReify gmw pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwReify gmw_nat32_reify gmw (unGmwNat share)
  _                                → undefined

foreign import ccall unsafe "&gmw_nat_drop" gmw_nat_drop ∷ FinalizerPtr CGmwNat

-- Delegation --

foreign import ccall unsafe "gmw_share_send_nat32" gmw_share_send_nat32 ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CUInt → IO ()

gmwShareSendNat ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → IPrecision → ℕ → m ()
gmwShareSendNat prg chans pr input = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ gmwShareSend gmw_share_send_nat32 prg chans $ HS.fromIntegral input
  _                                → undefined

foreign import ccall unsafe "gmw_share_recv_nat32" gmw_share_recv_nat32 ∷ Ptr CChannel → IO CUInt

gmwShareRecvNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℕ
gmwShareRecvNat chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwShareRecv gmw_share_recv_nat32 chan
  _                                → undefined

foreign import ccall unsafe "gmw_reveal_send_nat32" gmw_reveal_send_nat32 ∷ Ptr CChannel → CUInt → IO ()

gmwRevealSendNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℕ → m ()
gmwRevealSendNat chan pr output = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ gmwRevealSend gmw_reveal_send_nat32 chan $ HS.fromIntegral output
  _                                → undefined

foreign import ccall unsafe "gmw_reveal_recv_nat32" gmw_reveal_recv_nat32 ∷ Ptr (Ptr CChannel) → CSize → IO CUInt

gmwRevealRecvNat ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → IPrecision → m ℕ
gmwRevealRecvNat chans pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwRevealRecv gmw_reveal_recv_nat32 chans
  _                                → undefined

gmwShareRecvGmwNat ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → IPrecision → m GmwNat
gmwShareRecvGmwNat gmw chan pr = do
  z ← gmwShareRecvNat chan pr
  gmwNatNew gmw pr z

gmwRevealSendGmwNat ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → IPrecision → GmwNat → m ()
gmwRevealSendGmwNat gmw chan pr share = do
  z ← gmwNatReify gmw pr share
  gmwRevealSendNat chan pr z

--------------------------------
--- GMW Integer (Signed Int) ---
--------------------------------

foreign import ccall unsafe "gmw_int32_new" gmw_int32_new ∷ Ptr CGmw → CInt → IO (Ptr CGmwInt)

gmwIntNew ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → ℤ → m GmwInt
gmwIntNew gmw pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ GmwInt ^$ gmwReflect gmw_int32_new gmw_int_drop gmw $ HS.fromIntegral share
  _                                → undefined

foreign import ccall unsafe "gmw_int32_constant" gmw_int32_constant ∷ Ptr CGmw → CInt → IO (Ptr CGmwInt)

gmwIntConstant ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → ℤ → m GmwInt
gmwIntConstant gmw pr value = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ GmwInt ^$ gmwReflect gmw_int32_constant gmw_int_drop gmw $ HS.fromIntegral value
  _                                → undefined

foreign import ccall unsafe "gmw_int32_reify" gmw_int32_reify ∷ Ptr CGmw → Ptr CGmwInt → IO CInt

gmwIntReify ∷ (Monad m, MonadIO m) ⇒ Gmw → IPrecision → GmwInt → m ℤ
gmwIntReify gmw pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwReify gmw_int32_reify gmw (unGmwInt share)
  _                                → undefined

foreign import ccall unsafe "&gmw_int_drop" gmw_int_drop ∷ FinalizerPtr CGmwInt

-- Delegation --

foreign import ccall unsafe "gmw_share_send_int32" gmw_share_send_int32 ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CInt → IO ()

gmwShareSendInt ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → IPrecision → ℤ → m ()
gmwShareSendInt prg chans pr input = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ gmwShareSend gmw_share_send_int32 prg chans $ HS.fromIntegral input
  _                                → undefined

foreign import ccall unsafe "gmw_share_recv_int32" gmw_share_recv_int32 ∷ Ptr CChannel → IO CInt

gmwShareRecvInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℤ
gmwShareRecvInt chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwShareRecv gmw_share_recv_int32 chan
  _                                → undefined

foreign import ccall unsafe "gmw_reveal_send_int32" gmw_reveal_send_int32 ∷ Ptr CChannel → CInt → IO ()

gmwRevealSendInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℤ → m ()
gmwRevealSendInt chan pr output = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ gmwRevealSend gmw_reveal_send_int32 chan $ HS.fromIntegral output
  _                                → undefined

foreign import ccall unsafe "gmw_reveal_recv_int32" gmw_reveal_recv_int32 ∷ Ptr (Ptr CChannel) → CSize → IO CInt

gmwRevealRecvInt ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → IPrecision → m ℤ
gmwRevealRecvInt chans pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ gmwRevealRecv gmw_reveal_recv_int32 chans
  _                                → undefined

gmwShareRecvGmwInt ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → IPrecision → m GmwInt
gmwShareRecvGmwInt gmw chan pr = do
  z ← gmwShareRecvInt chan pr
  gmwIntNew gmw pr z

gmwRevealSendGmwInt ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → IPrecision → GmwInt → m ()
gmwRevealSendGmwInt gmw chan pr share = do
  z ← gmwIntReify gmw pr share
  gmwRevealSendInt chan pr z
