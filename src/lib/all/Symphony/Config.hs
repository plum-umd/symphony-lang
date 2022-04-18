module Symphony.Config where

import UVMHS

import Paths_symphony

import qualified Data.Version as Version

symphony_VERSION ∷ 𝕊
symphony_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

dataPath ∷ 𝕊 → IO 𝕊
dataPath = string ^∘ getDataFileName ∘ chars

findFile ∷ 𝕊 → IO 𝕊
findFile relative = do
  relativeExists ← pexists relative
  if relativeExists
  then return relative
  else dataPath relative
