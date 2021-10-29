module Allyn.Config where

import UVMHS

import Paths_allyn

import qualified Data.Version as Version

allyn_VERSION ∷ 𝕊
allyn_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

datapath ∷ 𝕊 → IO 𝕊
datapath = string ^∘ getDataFileName ∘ chars
