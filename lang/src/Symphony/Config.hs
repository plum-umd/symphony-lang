module Symphony.Config where

import UVMHS

import Paths_symphony

import qualified Data.Version as Version

symphony_VERSION ∷ 𝕊
symphony_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

datapath ∷ 𝕊 → IO 𝕊
datapath = string ^∘ getDataFileName ∘ chars
