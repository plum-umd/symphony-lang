module Main where

import UVMHS

import Symphony.Config
import Symphony.TypeChecker
import Symphony.TypeChecker.TLM
import Symphony.Interpreter
import Symphony.Interpreter.Types
import Symphony.Interpreter.Seq.Types
import Symphony.Interpreter.Dist.Types

import qualified Prelude as HS
import qualified Crypto.Random as R

symphonyMainExample ∷ IO ()
symphonyMainExample = do
  os :* ts ← parseOptionsSymphony
  name ← case ts of
    Nil      → failIO "ERROR: No file specified as target. Correct usage: symphony example [<arguments>] <name>"
    t :& Nil → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: symphony example [<arguments>] <name>"
  let exampleRelativePath = "examples/" ⧺ name ⧺ ".sym"
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
  tlsStd ← parseFile "lib:stdlib.sym" (optLibPath os ⧺ "/stdlib.sym")
  tlsPrg ← parseFile (concat ["example:",name,".sym"]) exampleRelativePath
  pptraceM tlsPrg
  
  g ← case optRandomSeed os of
        None   → R.drgNew
        Some n → return $ R.drgNewSeed $ R.seedFromInteger $ HS.fromIntegral n
  let tls = tlsStd ⧺ tlsPrg
 -- _τ ← evalTLMIO null null name $ synProg tls
 {-
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
-}
symphonyUsage ∷ 𝕊
symphonyUsage = "USAGE: symphony [options] file..."

symphonyInfo ∷ 𝕊
symphonyInfo =
  concat $ inbetween "\n"
  [ ""
  , "symphony is the interpreter for the Symphony language."
  , "Developed by UMD as an extension of the PSL language,"
  , "created by the PANTHEON team as part of the IARPA HECTOR project."
  , ""
  , symphonyUsage
  ]

symphonyMainInfo ∷ IO ()
symphonyMainInfo = out symphonyInfo

symphonyMain ∷ IO ()
symphonyMain = do
  map list iargs ≫= \case
    a :& as | a ≡ "example" → ilocalArgs as symphonyMainExample
    Nil             → ilocalArgs (list ["--version", "--help"]) symphonyMainInfo
    as              → ilocalArgs as symphonyMainInfo

main ∷ IO ()
main = do
  initUVMHS
  symphonyMain
