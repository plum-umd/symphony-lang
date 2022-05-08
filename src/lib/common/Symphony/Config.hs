module Symphony.Config where

import Symphony.Prelude

import Paths_symphony

import qualified Data.Version as Version

symphony_VERSION ∷ 𝕊
symphony_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

findSymphonyFile ∷ 𝕊 → 𝕊 → IO (𝑂 𝕊)
findSymphonyFile dir fn = do
  currentDir ← dcwd
  dataDir ← fromChars ^$ getDataDir
  findFile (frhs [ dir, currentDir, dataDir ]) fn
