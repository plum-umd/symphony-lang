module Symphony.TypeChecker.EM.Types where

import UVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.Env

data ER = ER
  { terSource ∷ 𝑂 SrcCxt
  , terMode   ∷ Mode
  , terEnv    ∷ Env
  , terModeScope    ∷ (𝕏 ⇰ Mode)
  }

type EW = ()

type ES = ()

type EE = Error

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
