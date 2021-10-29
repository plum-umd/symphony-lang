module Main where

import UVMHS

import Allyn.Config
import Allyn.TypeChecker
import Allyn.TypeChecker.Types
import Allyn.Interpreter
import Allyn.Interpreter.Types
import Allyn.Interpreter.Seq.Types
import Allyn.Interpreter.Dist.Types

import qualified Prelude as HS
import qualified Crypto.Random as R

allynMainExample ∷ IO ()
allynMainExample = do
  os :* ts ← parseOptionsAllyn
  name ← case ts of
    Nil      → failIO "ERROR: No file specified as target. Correct usage: allyn example [<arguments>] <name>"
    t :& Nil → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: allyn example [<arguments>] <name>"
  let exampleRelativePath = "examples/" ⧺ name ⧺ ".all"
  exampleDataFilePath ← datapath exampleRelativePath
  exampleLocalExists ← pexists exampleRelativePath
  exampleDataFileExists ← pexists exampleDataFilePath
  when (not exampleLocalExists ⩓ exampleDataFileExists) $ do
    dtouch "examples"
    fcopy exampleDataFilePath exampleRelativePath
  pprint $ ppHorizontal
    [ ppHeader "INTERPRETING EXAMPLE:"
    , ppString name
    ]
  let θ = update iParamsIsExampleL True $ initializeEnv os
  tlsStd ← parseFile "lib:stdlib.all" (optLibPath os ⧺ "/stdlib.all")
  tlsPrg ← parseFile (concat ["example:",name,".all"]) exampleRelativePath
  g ← case optRandomSeed os of
        None   → R.drgNew
        Some n → return $ R.drgNewSeed $ R.seedFromInteger $ HS.fromIntegral n
  let tls = tlsStd ⧺ tlsPrg
--  runTMIO null name $ wellTyped tls
  if isSome (iParamsMe θ) then do
    let prog = do
          interpTLs tls
          interpMain
    v ← evalITLMIO @DistVal θ (ωtl₀ g) name prog
    pprint $ ppHeader "RESULT"
    pprint v
  else do
    let prog = do
          interpTLs tls
          interpMain
    v ← evalITLMIO @SeqVal θ (ωtl₀ g) name prog
    pprint $ ppHeader "RESULT"
    pprint v

allynUsage ∷ 𝕊
allynUsage = "USAGE: allyn [options] file..."

allynInfo ∷ 𝕊
allynInfo =
  concat $ inbetween "\n"
  [ ""
  , "allyn is the interpreter for the Allyn language."
  , "Developed by UMD as an extension of the PSL language,"
  , "created by the PANTHEON team as part of the IARPA HECTOR project."
  , ""
  , allynUsage
  ]

allynMainInfo ∷ IO ()
allynMainInfo = out allynInfo

allynMain ∷ IO ()
allynMain = do
  map list iargs ≫= \case
    a :& as | a ≡ "example" → ilocalArgs as allynMainExample
    Nil             → ilocalArgs (list ["--version", "--help"]) allynMainInfo
    as              → ilocalArgs as allynMainInfo

main ∷ IO ()
main = do
  initUVMHS
  allynMain
