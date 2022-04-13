module Main where

import Symphony.Prelude
import Symphony.Config

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Seq
import Symphony.Dynamic.Seq.Types
import Symphony.Dynamic.Seq.Seq.Types
import Symphony.Dynamic.Seq.Seq.Val

import qualified Prelude as HS
import qualified Crypto.Random as R
import qualified System.Console.GetOpt as O

data Options = Options
  { optVersion ∷ 𝔹
  , optHelp ∷ 𝔹
  , optRandomSeed ∷ 𝑂 ℕ
  , optParty ∷ 𝑂 Prin
  , optTestsPath ∷ 𝕊
  , optLibPath ∷ 𝕊
  }
  deriving (Eq,Ord,Show)
makeLenses ''Options

options₀ ∷ IO Options
options₀ = do
  testsPath ← findFile "tests"
  libPath   ← findFile "lib"
  return $ Options
    { optVersion = False
    , optHelp = False
    , optRandomSeed = None
    , optParty = None
    , optTestsPath = testsPath
    , optLibPath = libPath
    }

usageInfoTop ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTop = frhs
  [ O.Option ['v'] [chars "version"]
             (O.NoArg $ update optVersionL True)
           $ chars "print version"
  , O.Option ['h'] [chars "help"]
             (O.NoArg $ update optHelpL True)
           $ chars "show help"
  ]

usageInfoRun ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoRun = frhs
  [ O.Option ['P'] [chars "party"]
             (O.ReqArg (\ s → update optPartyL $ Some $ string s) $ chars "PRIN")
           $ chars "set current party"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoExample ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoExample = frhs
  [ O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

usageInfoTest ∷ 𝐿 (O.OptDescr (Options → Options))
usageInfoTest = frhs
  [ O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optRandomSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

readPrinVal ∷ 𝕊 → 𝑂 PrinVal
readPrinVal s = case list $ splitOn𝕊 "." s of
  ρ :& Nil      → Some $ SinglePV ρ
  ρ :& n :& Nil → Some $ AccessPV ρ (read𝕊 n)
  _             → None

initializeEnv ∷ Options → IParams
initializeEnv os = flip compose θ₀
  [ update iParamsMeL $ mjoin $ readPrinVal ^$ optParty os ]

parseOptionsSymphony ∷ IO (Options ∧ 𝐿 𝕊)
parseOptionsSymphony = do
  as ← iargs
  let fs :* nos :* ems = parseOptions (usageInfoTop ⧺ usageInfoRun) as
  eachOn ems out
  os ← compose fs ^$ options₀
  when (optVersion os) $ do
    out $ "symphony version " ⧺ symphony_VERSION
  when (optVersion os ⩓ optHelp os) $ do
    out ""
  when (optHelp os) $ do
    out "Usage: symphony [<command>] [<arguments>] [<target>]"
    out ""
    out $ optUsageInfo "symphony [arguments]" usageInfoTop
    out $ optUsageInfo "symphony run [arguments] <file>" usageInfoRun
    out $ optUsageInfo "symphony example [arguments] <name>"  usageInfoExample
    out $ optUsageInfo "symphony test [arguments]" usageInfoTest
  return $ os :* nos

symphonyMainExample ∷ IO ()
symphonyMainExample = do
  os :* ts ← parseOptionsSymphony
  name ← case ts of
    Nil      → failIO "ERROR: No file specified as target. Correct usage: symphony example [<arguments>] <name>"
    t :& Nil → return t
    _ → failIO "ERROR: Too many files specified as target. Correct usage: symphony example [<arguments>] <name>"
  examplePath ← findFile $ "bin/" ⧺ name ⧺ ".sym"
  pprint $ ppHorizontal
    [ ppHeader "INTERPRETING EXAMPLE:"
    , ppString name
    ]
  let θ = update iParamsIsExampleL True $ initializeEnv os
  tlsStd ← parseFile "lib:stdlib.sym" (optLibPath os ⧺ "/stdlib.sym")
  tlsPrg ← parseFile (concat ["example:",name,".sym"]) examplePath
  g ← case optRandomSeed os of
        None   → R.drgNew
        Some n → return $ R.drgNewSeed $ R.seedFromInteger $ HS.fromIntegral n
  let tls = tlsStd ⧺ tlsPrg
  if isSome (iParamsMe θ) then do
#if DIST
    let prog = do
          interpTLs tls
          interpMain
    v ← evalITLMIO @DistVal θ (ωtl₀ g) name prog
    pprint $ ppHeader "RESULT"
    pprint v
#else
    return ()
#endif
  else do
    let prog = do
          interpTLs tls
          interpMain
    v ← evalITLMIO @SeqVal θ (ωtl₀ g) name prog
    pprint $ ppHeader "RESULT"
    pprint v

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
    Nil                     → ilocalArgs (list ["--version", "--help"]) symphonyMainInfo
    as                      → ilocalArgs as symphonyMainInfo

main ∷ IO ()
main = do
  initUVMHS
  symphonyMain
