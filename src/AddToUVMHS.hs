module AddToUVMHS 
  ( module AddToUVMHS
  , module UVMHS
  , module GHC.Stack
  ) where

import UVMHS

import Paths_psl

import GHC.Stack (CallStack,callStack,withFrozenCallStack)

import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import qualified Data.Version as Version
import qualified System.Directory as Directory
import qualified System.FilePath.Posix as FP
import qualified Data.ByteString as BS

success ∷ (Monad m) ⇒ m a → FailT m a
success xM = FailT $ Some ^$ xM

-- instance DivMod 𝔻 where {(⌿) = (HS./);(÷) = HS.mod'}

writeAppend ∷ 𝕊 → 𝕊 → IO ()
writeAppend = Text.appendFile ∘ chars

pathFn ∷ 𝕊 → 𝕊
pathFn = string ∘ FP.takeFileName ∘ chars

pathBn ∷ 𝕊 → 𝕊
pathBn = string ∘ FP.takeBaseName ∘ chars

pathDir ∷ 𝕊 → 𝕊
pathDir = string ∘ FP.takeDirectory ∘ chars

pathExt ∷ 𝕊 → 𝕊
pathExt = string ∘ FP.takeExtension ∘ chars

rmDirs ∷ 𝕊 → IO ()
rmDirs = Directory.removeDirectoryRecursive ∘ chars

pathExists ∷ 𝕊 → IO 𝔹
pathExists = Directory.doesPathExist ∘ chars

split ∷ (ToStream (a ∧ b) t) ⇒ t → 𝑆 a ∧ 𝑆 b
split (stream → xs) = map fst xs :* map snd xs

getDataFilePath ∷ 𝕊 → IO 𝕊
getDataFilePath = string ^∘ getDataFileName ∘ chars

psl_VERSION ∷ 𝕊
psl_VERSION = concat $ inbetween "." $ map show𝕊 $ Version.versionBranch version

copyFile ∷ 𝕊 → 𝕊 → IO ()
copyFile fr to = Directory.copyFile (chars fr) $ chars to

readFile ∷ 𝕊 → IO 𝕊
readFile = Text.decodeUtf8 ^∘ BS.readFile ∘ chars

writeFile ∷ 𝕊 → 𝕊 → IO ()
writeFile file = BS.writeFile (chars file) ∘ Text.encodeUtf8
