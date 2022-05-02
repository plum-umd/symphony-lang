module Symphony.TypeChecker.TLM.Types where

import UVMHS

import Symphony.TypeChecker.Env
import Symphony.TypeChecker.Error

data TLR = TLR
  { ttlrSource ∷ 𝑂 SrcCxt
  }

type TLW = ()

data TLS = TLS
  { ttlsEnv ∷ Env,
  ttlsPrins ∷ (𝑃 𝕏),
  }

type TLE = Error

newtype TLM a = TTLM { unTLM ∷ RWST TLR TLW TLS (ErrorT TLE ID) a }
  deriving
    ( Functor
    , Return, Bind, Monad
    , MonadReader TLR
    , MonadWriter TLW
    , MonadState TLS
    , MonadError TLE
    )

makeLenses ''TLR
makeLenses ''TLS
