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

foreign import ccall unsafe "&gmw_delete" gmw_delete ∷ FinalizerPtr CGmw

foreign import ccall unsafe "gmw_create" gmw_create ∷ CSize → CSize → Ptr (Ptr CChannel) → IO (Ptr CGmw)

gmwCreate ∷ (Monad m, MonadIO m) ⇒ PrinVal → (PrinVal ⇰ Channel) → m Gmw
gmwCreate me chans = io $
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  Gmw ^$ newForeignPtr gmw_delete *$ gmw_create cme (HS.fromIntegral len_cchans) cchans_ptr
  where cme    = HS.fromIntegral $ fromSome $ idsFr (keys chans) ⋕? me
        cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans

foreign import ccall unsafe "&gmw_bool_delete" gmw_bool_delete ∷ FinalizerPtr CGmwBool

foreign import ccall unsafe "gmw_share_send_bool" gmw_share_send_bool ∷ Ptr CPrg → CSize → Ptr (Ptr CChannel) → CBool → IO ()

gmwShareSendBool ∷ (Monad m, MonadIO m) ⇒ Prg → (PrinVal ⇰ Channel) → 𝔹 → m ()
gmwShareSendBool prg chans input = io $
  withForeignPtr cprg $ \ cprg_ptr →
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  gmw_share_send_bool cprg_ptr (HS.fromIntegral len_cchans) cchans_ptr cinput
  where cprg   = unPrg prg
        cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans
        cinput = fromBool input

foreign import ccall unsafe "gmw_share_recv_bool" gmw_share_recv_bool ∷ Ptr CGmw → Ptr CChannel → IO (Ptr CGmwBool)

gmwShareRecvBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → m GmwBool
gmwShareRecvBool gmw chan = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  withForeignPtr cchan $ \ cchan_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_delete *$ gmw_share_recv_bool cgmw_ptr cchan_ptr
  where cgmw  = unGmw gmw
        cchan = unChannel chan

foreign import ccall unsafe "gmw_reveal_send_bool" gmw_reveal_send_bool ∷ Ptr CGmw → Ptr CChannel → Ptr CGmwBool → IO ()

gmwRevealSendBool ∷ (Monad m, MonadIO m) ⇒ Gmw → Channel → GmwBool → m ()
gmwRevealSendBool gmw chan output = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  withForeignPtr cchan $ \ cchan_ptr →
  withForeignPtr coutput $ \ coutput_ptr →
  gmw_reveal_send_bool cgmw_ptr cchan_ptr coutput_ptr
  where cgmw    = unGmw gmw
        cchan   = unChannel chan
        coutput = unGmwBool output

foreign import ccall unsafe "gmw_reveal_recv_bool" gmw_reveal_recv_bool ∷ CSize → Ptr (Ptr CChannel) → IO CBool

gmwRevealRecvBool ∷ (Monad m, MonadIO m) ⇒ (PrinVal ⇰ Channel) → m 𝔹
gmwRevealRecvBool chans = io $
  withForeignPtrs cchans $ \ cchan_ptrs →
  withArrayLen cchan_ptrs $ \ len_cchans cchans_ptr →
  toBool ^$ gmw_reveal_recv_bool (HS.fromIntegral len_cchans) cchans_ptr
  where cchans = tohs $ list $ map (unChannel ∘ snd) $ iter chans

foreign import ccall unsafe "gmw_lit_bool" gmw_lit_bool ∷ Ptr CGmw → CBool → IO (Ptr CGmwBool)

gmwLitBool ∷ (Monad m, MonadIO m) ⇒ Gmw → 𝔹 → m GmwBool
gmwLitBool gmw input = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_delete *$ gmw_lit_bool cgmw_ptr cinput
  where cgmw   = unGmw gmw
        cinput = fromBool input

foreign import ccall unsafe "gmw_and_bool" gmw_and_bool ∷ Ptr CGmw → Ptr CGmwBool → Ptr CGmwBool → IO (Ptr CGmwBool)

gmwAndBool ∷ (Monad m, MonadIO m) ⇒ Gmw → GmwBool → GmwBool → m GmwBool
gmwAndBool gmw inp₁ inp₂ = io $
  withForeignPtr cgmw $ \ cgmw_ptr →
  withForeignPtr cinp₁ $ \ cinp₁_ptr →
  withForeignPtr cinp₂ $ \ cinp₂_ptr →
  GmwBool ^$ newForeignPtr gmw_bool_delete *$ gmw_and_bool cgmw_ptr cinp₁_ptr cinp₂_ptr
  where cgmw  = unGmw gmw
        cinp₁ = unGmwBool inp₁
        cinp₂ = unGmwBool inp₂

{-
getGmwSession ∷ 𝑃 PrinVal → IM Val (𝑂 Gmw)
getGmwSession ρvs = do
  πs ← getL iStateSessionsGmwL
  return $ πs ⋕? ρvs

mkGmwSession ∷ 𝑃 PrinVal → IM Val Gmw
mkGmwSession ρvs = do
  π ← todoCxt
  modifyL iStateSessionsGmwL ((ρvs ↦ π) ⩌!)
  return π

getOrMkSessionGmw ∷ 𝑃 PrinVal → IM Val Gmw
getOrMkSessionGmw ρvs = do
  π𝑂 ← getGmwSession ρvs
  case π𝑂 of
    None   → mkGmwSession ρvs
    Some π → return π
-}


-- Values
{-
gmwShareSend ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → ClearBaseVal → IM Val ()
gmwShareSend _ρvFr ρvsTo cbv = do
  prg   ← getPrg
  chans ← getChannels ρvsTo
  case cbv of
    BulV    → return ()
    BoolV b → gmwShareSendBool prg chans b
    _       → todoCxt

gmwShareRecv ∷ (STACK) ⇒ PrinVal → 𝑃 PrinVal → BaseType → IM Val GmwBaseVal
gmwShareRecv ρvsFr ρvsTo bτ = do
  gmw  ← gmwGetOrMkSession ρvsTo
  chan ← getChannel ρvFr
  case bτ of
    UnitT → return BulGBV
    𝔹T    → BoolGBV ^$ gmwShareRecvBool gmw chan
    _     → todoCxt

gmwRevealSend ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → GmwBaseVal → IM Val ()
gmwRevealSend ρvsFr ρvTo output = do
  gmw  ← gmwGetOrMkSession ρvsFr
  chan ← getChannel ρvTo
  case output of
    BulGBV    → return ()
    BoolGBV b → gmwRevealSendBool gmw chan b
    _         → todoCxt

gmwRevealRecv ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → BaseType → IM Val ClearBaseVal
gmwRevealRecv ρvsFr _ρvTo bτ = do
  chans ← getChannels ρvsFr
  case bτ of
    UnitT → return BulV
    𝔹T    → gmwRevealRecvBool chans
    _     → todoCxt

revealSendGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Gmw → IM Val ()
revealSendGmw ρvsFr ρvsTo sh = do
  π ← getOrMkSessionGmw ρvsFr
  chansTo ← getOrMkChannels ρvsTo
  todoCxt

revealRecvGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val ClearBaseVal
revealRecvGmw ρvsFr ρvsTo bτ = do
  chansFr ← getOrMkChannels ρvsFr
  todoCxt

embedGmw ∷ 𝑃 PrinVal → ClearBaseVal → IM Val Gmw
embedGmw ρvs cbv = do
  π ← getOrMkSessionGmw ρvs
  todoCxt

primGmw ∷ 𝑃 PrinVal → Op → 𝐿 Gmw → IM Val Gmw
primGmw ρvs op sh = do
  π ← getOrMkSessionGmw ρvs
  todoCxt
-}
