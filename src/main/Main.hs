module Main where

import Symphony.Prelude hiding (parseOptions)
import qualified Prelude as HS

import Options
import Command

main ∷ IO ()
main = do
  initUVMHS
  symphonyMain

symphonyMain ∷ IO ()
symphonyMain = do
  args ← iargs
  opts :* cmdArgs ← execExceptIO $ parseOptions args
  when (optHelp opts) $ do
    out helpMsg
    exitIO
  when (optVersion opts) $ do
    out versionMsg
    exitIO
  cmd :* argsLeft ← execExceptIO $ parseCommand cmdArgs
  r ← mjoin $ execErrorTIO $ runCommand cmd argsLeft
  out $ ppRender r

versionMsg ∷ 𝕊
versionMsg = "symphony 0.0.0"
