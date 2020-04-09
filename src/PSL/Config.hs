module PSL.Config where

import UVMHS

import Paths_psl

import qualified Data.Version as Version

psl_VERSION ∷ 𝕊
psl_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

datapath ∷ 𝕊 → IO 𝕊
datapath = string ^∘ getDataFileName ∘ chars
