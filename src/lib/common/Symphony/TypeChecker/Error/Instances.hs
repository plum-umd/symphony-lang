module Symphony.TypeChecker.Error.Instances where

import UVMHS

import Symphony.TypeChecker.Error.Types

makePrettySum ''Class

instance Pretty Error where
  pretty (Error rsO cs rc rm) = ppVertical $ concat
    [ single𝐼 $ ppHeader $ show𝕊 rc
    , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
    , single𝐼 $ rm
    , single𝐼 $ pretty cs
    ]
