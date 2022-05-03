module Symphony.TypeChecker.Error.Types where

import UVMHS

data Class =
    TypeError
  | NotImplementedError
  | InternalError
  deriving (Eq, Ord, Show)

data Error = Error
  { teSource    ∷ 𝑂 SrcCxt
  , teCallStack ∷ CallStack
  , teClass     ∷ Class
  , teMsg       ∷ Doc
  }
