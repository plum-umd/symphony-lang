module Symphony.TypeChecker.TLM.Instances where

import UVMHS

import Symphony.TypeChecker.TLM.Types

instance HasLens TLR (𝑂 SrcCxt) where
  hasLens = ttlrSourceL

instance Null TLR where
  null = TLR { ttlrSource = None }

instance Null TLS where
  null = TLS { ttlsEnv = null, ttlsPrins = null }
