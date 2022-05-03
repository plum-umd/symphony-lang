module Symphony.TypeChecker.EM.Instances where

import UVMHS

import Symphony.TypeChecker.EM.Types

instance HasLens ER (𝑂 SrcCxt) where
  hasLens = terSourceL
