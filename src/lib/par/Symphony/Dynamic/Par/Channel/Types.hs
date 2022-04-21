module Symphony.Dynamic.Par.Channel.Types where

import Symphony.Prelude
import qualified Prelude as HS
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Data.Word

type CChannel = ()
newtype Channel = Channel { unChannel ∷ ForeignPtr CChannel } deriving (Eq, Ord, Show)

type Addr   = 𝕊
type HSAddr = HS.String
type CAddr  = CString

type Port   = ℕ16
type HSPort = Word16
type CPort  = CUShort
