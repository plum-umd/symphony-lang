module Symphony.TypeChecker.TLM.Types where

import UVMHS

import Symphony.TypeChecker.Env

type TLR = ()

type TLW = ()

data TLS = TTLS
  { ttlsEnv ∷ Env
  }

data TLEClass =
    TypeError
  | NotImplementedError
  | InternalError
  deriving (Eq, Ord, Show)

data TLE = TTLE
  { ttleClass ∷ TLEClass
  }

newtype TLM a = TTLM { unTTLM ∷ RWST TLR TLW TLS (ErrorT TLE ID) a }
  deriving
    ( Functor
    , Return, Bind, Monad
    , MonadReader TLR
    , MonadWriter TLW
    , MonadState TLS
    , MonadError TLE
    )

makeLenses ''TLS
