module Symphony.Interpreter.NetIO where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Interpreter.Types

import Symphony.Interpreter.Error

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String
import Foreign.Marshal.Alloc

import qualified Prelude as HS
import qualified Data.Text as T
import qualified Data.ByteString as BS

foreign import ccall unsafe "backend-emp.h netio_create" netio_create ∷ CString → HS.Int → HS.Bool → IO (Ptr NetIOStruct)
foreign import ccall unsafe "backend-emp.h netio_send" netio_send ∷ Ptr NetIOStruct → Ptr a → HS.Int → IO ()
foreign import ccall unsafe "backend-emp.h netio_recv" netio_recv ∷ Ptr NetIOStruct → Ptr a → HS.Int → IO ()
foreign import ccall unsafe "backend-emp.h netio_flush" netio_flush ∷ Ptr NetIOStruct → IO ()
foreign import ccall unsafe "backend-emp.h netio_socket" netio_socket ∷ Ptr NetIOStruct → IO CInt
foreign import ccall unsafe "backend-emp.h &netio_destroy" netio_destroy ∷ FinalizerPtr NetIOStruct

assignRoles ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → PrinVal → m (PrinVal ∧ PrinVal)
assignRoles ρv₁ ρv₂ = if ρv₁ < ρv₂ then return (ρv₁ :* ρv₂) else if ρv₂ < ρv₁ then return (ρv₂ :* ρv₁) else impossibleCxt

localhost ∷ HS.String
localhost = T.unpack "127.0.0.1"

netIOBasePort ∷ ℕ
netIOBasePort = 12345

netIOPortOf ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → m ℕ
netIOPortOf ρv = do
  prinScope ← askL iCxtPrinScopeL
  let netIOPorts = map (\ n → netIOBasePort + n) $ idsFr prinScope
  fromSomeCxt $ netIOPorts ⋕? ρv

netIOCreate ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadIO m) ⇒ PrinVal → PrinVal → 𝔹 → m NetIO
netIOCreate ρvMe ρvThem quiet = do
  ρvClient :* ρvServer ← assignRoles ρvMe ρvThem
  let withAddr = if ρvMe ≡ ρvClient then (withCString localhost) else withNullPtr
  port ← netIOPortOf ρvServer
  io $ withAddr $ \ addr → newForeignPtr netio_destroy *$ netio_create addr (HS.fromIntegral port) quiet
  where withNullPtr k = k nullPtr

netIOFlush ∷ NetIO → IO ()
netIOFlush net = withForeignPtr net netio_flush

netIOSocket ∷ NetIO → IO CInt
netIOSocket net = withForeignPtr net netio_socket

netIOSendStorable ∷ (Storable a) ⇒ NetIO → a → IO ()
netIOSendStorable net v =
  withForeignPtr net $ \ netp →
  alloca $ \ buf → do
    poke buf v
    netio_send netp buf $ sizeOf v

netIORecvStorable ∷ forall a . (Storable a) ⇒ NetIO → IO a
netIORecvStorable net =
  withForeignPtr net $ \ netp →
  alloca $ \ buf → do
    netio_recv netp buf $ sizeOf (undefined ∷ a)
    peek buf

-- TODO(ins): Can make send/recv do less copying (by using unsafe variants) if necessary

netIOSend ∷ NetIO → BS.ByteString → IO ()
netIOSend net bin =
  withForeignPtr net $ \ netp →
  BS.useAsCStringLen bin $ \ (buf, sz) →
  netio_send netp buf sz

netIORecv ∷ NetIO → HS.Int → IO BS.ByteString
netIORecv net sz =
  withForeignPtr net $ \ netp →
  allocaBytes sz $ \ buf → do
    netio_recv netp buf sz
    BS.packCStringLen (buf, sz)
