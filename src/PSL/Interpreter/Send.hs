module PSL.Interpreter.Send where

import UVMHS

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

unixPathAddr ∷ PrinVal → PrinVal → HS.String
unixPathAddr ρv₁ ρv₂ = Text.unpack $ concat ["/tmp/psl-", ppshow ρv₁, ppshow ρv₂]

-- Example: serializeVal ConsV(0{A}, ConsV(1{A}, Nil{A})) = toJSON ConsV(?:ℤ{A}, ?:[ℤ]{A})
serializeVal ∷ Val → BS.ByteString
serializeVal = \case
  NilV      → Text.encodeUtf8 "nil"
  ConsV _ _ → Text.encodeUtf8 "cons"

deserializeVal ∷ PrinVal → BS.ByteString → Val
deserializeVal ρv s = case Text.decodeUtf8 s of
  "nil"  → NilV
  "cons" → ConsV consHd consTl
  where consHd = SSecVP (SecM $ single𝑃 ρv) $ UnknownV $ BaseT $ ℤT iprDefault
        consTl = SSecVP (SecM $ single𝑃 ρv) $ UnknownV $ ListT $ BaseT $ ℤT iprDefault

localhost ∷ HostName
localhost = Text.unpack "127.0.0.1"

sendPort ∷ ServiceName
sendPort = Text.unpack "49200"

hints = defaultHints { addrSocketType = Stream }

getMyAddrInfo ∷ IO AddrInfo
getMyAddrInfo = HS.head HS.<$> getAddrInfo (HS.Just hints) (HS.Just localhost) (HS.Just sendPort)

sendVal ∷ Val → IO ()
sendVal v = withSocketsDo $ do
  pptraceM v
  addr ← getMyAddrInfo
  sock ← tryConnect addr
  pptraceM "connected"
  let vs = serializeVal v
  sendAll sock vs
  close sock
  where tryConnect a = do
          pptraceM "connecting..."
          sock ← socket (addrFamily a) (addrSocketType a) (addrProtocol a)
          result ← E.try @E.IOException $ connect sock $ addrAddress a
          case result of
            HS.Left _   → do
              close sock
              threadDelay (HS.fromIntegral 1000000)
              tryConnect a
            HS.Right () → return sock

recvVal ∷ PrinVal → IO Val
recvVal ρvS = withSocketsDo $ do
  pptraceM "receiving..."
  addr ← getMyAddrInfo
  sock ← socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
  setSocketOption sock ReuseAddr (HS.fromIntegral 1)
  bind sock $ addrAddress addr
  listen sock (HS.fromIntegral 1024)
  pptraceM "listening..."
  (conn, _) ← accept sock
  pptraceM "accepted"
  vs ← recvAll conn BS.empty
  let v = deserializeVal ρvS vs
  pptraceM v
  close conn
  close sock
  return v
  where recvAll conn sofar = do
          msg ← Network.Socket.ByteString.recv conn (HS.fromIntegral 1024)
          if BS.null msg then
            return sofar
          else do
            recvAll conn (BS.append sofar msg)
