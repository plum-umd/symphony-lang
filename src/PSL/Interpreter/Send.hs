module PSL.Interpreter.Send where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Json

import qualified Data.ByteString as BS
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Control.Exception as E
import qualified Data.Aeson as JSON

import qualified Prelude as HS

import Network.Socket
import Network.Socket.ByteString
import Control.Concurrent
import Foreign.C.Error

unixPathAddr ∷ PrinVal → PrinVal → HS.String
unixPathAddr ρv₁ ρv₂ = Text.unpack $ concat ["/tmp/psl-", ppshow ρv₁, ppshow ρv₂]

whoAmI ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ m PrinVal
whoAmI = do
  lm ← askL iCxtLocalModeL
  fromSomeCxt $ view (one𝑃L ⊚ secML) lm

-- Example: serializeVal ConsV(0{A}, ConsV(1{A}, Nil{A})) = toJSON ConsV(?:ℤ{A}, ?:[ℤ]{A})
serializeValNR ∷ Val → BS.ByteString
serializeValNR v = BS.empty
{-  \case
  NilV      → Text.encodeUtf8 "nil"
  ConsV _ _ → Text.encodeUtf8 "cons" -}

deserializeValNR ∷ BS.ByteString → Val
deserializeValNR s = DefaultV
{-
  case Text.decodeUtf8 s of
  "nil"  → NilV
  "cons" → ConsV consHd consTl
  where consHd = SSecVP (SecM $ single𝑃 ρv) $ UnknownV $ BaseT $ ℤT iprDefault
        consTl = SSecVP (SecM $ single𝑃 ρv) $ UnknownV $ ListT $ BaseT $ ℤT iprDefault -}

serializeValR ∷ Val → BS.ByteString
serializeValR v = BS.empty

deserializeValR ∷ BS.ByteString → Val
deserializeValR s = DefaultV

localhost ∷ HostName
localhost = Text.unpack "127.0.0.1"

portPSL ∷ PortNumber
portPSL = HS.fromIntegral 49150

getLHAddrInfo ∷ AddrInfo → PortNumber → IO AddrInfo
getLHAddrInfo hints port = HS.head HS.<$> getAddrInfo (HS.Just hints) (HS.Just localhost) (HS.Just $ show port)

connectHints ∷ AddrInfo
connectHints = defaultHints { addrSocketType = Stream } -- Use TCP

sendVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ (Val → BS.ByteString) → Val → PrinVal → m ()
sendVal serialize v ρvR = do
  portMap ← getPortMap portPSL
  port    ← fromSomeCxt $ portMap ⋕? ρvR
  io $ withSocketsDo $ do
    addr    ← getLHAddrInfo connectHints port
    pptraceM "Connecting..."
    sock    ← tryConnect addr
    pptraceM "Connected..."
    sendAll sock $ serialize v
    close sock
  where tryConnect a = do
          sock ← socket (addrFamily a) (addrSocketType a) (addrProtocol a)
          r    ← E.try @E.IOException $ connect sock $ addrAddress a
          case r of
            HS.Left e → do
              close sock
              threadDelay (HS.fromIntegral 10000) -- TODO(ins): Don't know if this is necessary, seems like a good idea
              tryConnect a
            HS.Right () → return sock

sendValR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ Val → PrinVal → m ()
sendValR v ρv = return ()

sendEncValR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ Val → PrinVal → m ()
sendEncValR v ρv = return ()

sendValNR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ Val → PrinVal → m ()
sendValNR = sendVal serializeValNR

recvVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ (BS.ByteString → Val) → PrinVal → m Val
recvVal deserialize ρvS = do

  portMap      ← getPortMap portPSL

  portExpected ← fromSomeCxt $ portMap ⋕? ρvS
  osock        ← getL iStateListenSockL
  sock         ← case osock of
                   None → do
                     me     ← whoAmI
                     myPort ← fromSomeCxt $ portMap ⋕? me
                     sock   ← io $ listenSock myPort
                     putL iStateListenSockL $ Some sock
                     return sock
                   Some sock → return sock
  vs           ← io $ withSocketsDo $ do
    pptraceM "Accepting..."
    (conn, addr) ← accept sock
    pptraceM "Accepted..."
    case addr of -- Just a sanity check to make sure we are receiving data from the expected party
      SockAddrInet portActual _ → assert (portExpected ≡ portActual) $ return ()
      _                         → impossible
    vs ← recvAll conn
    close conn
    return vs
  return $ deserialize vs
  where recvAll conn = recvAllR conn BS.empty
        recvAllR conn sofar = do
          msg ← Network.Socket.ByteString.recv conn (HS.fromIntegral 1024)
          if BS.null msg then
            return sofar
          else
            recvAllR conn (BS.append sofar msg)

recvValR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ PrinVal → m Val
recvValR = recvVal deserializeValR

recvEncValR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ PrinVal → m Val
recvEncValR ρv = return UnknownV

recvValNR ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ PrinVal → m Val
recvValNR = recvVal deserializeValNR

listenHints ∷ AddrInfo
listenHints = defaultHints { addrFlags = [AI_PASSIVE] , addrSocketType = Stream } -- Accept any connection, use TCP

listenSock ∷ PortNumber → IO Socket
listenSock port = withSocketsDo $ do
  addrInfo ← getLHAddrInfo listenHints port
  sock     ← socket (addrFamily addrInfo) (addrSocketType addrInfo) (addrProtocol addrInfo)
  setSocketOption sock ReuseAddr $ HS.fromIntegral 1
  bind sock $ addrAddress addrInfo
  listen sock $ HS.fromIntegral 1024
  pptraceM "Listening..."
  return sock
