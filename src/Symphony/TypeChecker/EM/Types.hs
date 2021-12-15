module Symphony.TypeChecker.EM.Types where

import UVMHS

import Symphony.TypeChecker.Env

data ER = ER
  { terEnv ∷ Env
  }

type EW = ()

type ES = ()

data EEClass =
    TypeError
  | NotImplementedError
  | InternalError
  deriving (Eq, Ord, Show)

data EE = EE
  { teeClass ∷ EEClass
  }

newtype EM a = EM { unEM ∷ RWST ER EW ES (ErrorT EE ID) a }
  deriving
    ( Functor
    , Return, Bind, Monad
    , MonadReader ER
    , MonadWriter EW
    , MonadState ES
    , MonadError EE
    )

makeLenses ''ER
