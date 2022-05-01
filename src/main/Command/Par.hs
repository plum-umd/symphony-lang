module Command.Par where

import Symphony.Prelude
import Symphony.Config
import qualified Prelude as HS

import Options

import Symphony.Lang.Syntax
import Symphony.Lang.Parser
-- TODO(ins): Should remove CPP here and instead add stub module for Par to Symphony library
#ifdef PAR
import Symphony.Dynamic.Par
import Symphony.Dynamic.Par.Prg
import Symphony.Dynamic.Par.Channel
#endif

import qualified System.Console.GetOpt as O

data OptionsPar = OptionsPar
  { optParHelp   ∷ 𝔹
  , optParParty  ∷ 𝑂 𝕊
  , optParConfig ∷ 𝑂 𝕊
  , optParSeed   ∷ 𝑂 ℕ
  }
makeLenses ''OptionsPar

optionsPar₀ ∷ OptionsPar
optionsPar₀ = OptionsPar
  { optParHelp   = False
  , optParParty  = None
  , optParConfig = None
  , optParSeed   = None
  }

optionsParDescr ∷ 𝐿 (O.OptDescr (OptionsPar → OptionsPar))
optionsParDescr = frhs
  [ O.Option ['h'] [chars "help"]
             (O.NoArg $ update optParHelpL True)
           $ chars "show help"
  , O.Option ['p'] [chars "party"]
             (O.ReqArg (\ s → update optParPartyL $ Some $ build𝕊C s) $ chars "PARTY")
           $ chars "set current party"
  , O.Option ['c'] [chars "config"]
             (O.ReqArg (\ s → update optParConfigL $ Some $ build𝕊C s) $ chars "PATH")
           $ chars "parties configuration as <id,address,port>..."
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optParSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

parseOptionsPar ∷ 𝐿 𝕊 → Except OptionsParError (OptionsPar ∧ 𝐿 𝕊)
parseOptionsPar args = do
  when isError $ throw (OptionsParError errs)
  return $ options :* argsLeft
  where optionsMods :* argsLeft :* errs = Symphony.Prelude.parseOptions optionsParDescr args
        isError = not $ isEmpty errs
        options = compose optionsMods optionsPar₀

helpParMsg ∷ 𝕊
helpParMsg = fromChars $ O.usageInfo header $ tohs optionsParDescr
  where header = chars $ concat [ "USAGE:\n"
                                , "    symphony par [OPTIONS] <PATH>\n"
                                , "\n"
                                , "OPTIONS:"
                                ]

data OptionsParError = OptionsParError { getOptParErrMsgs ∷ 𝐿 𝕊 }

instance Pretty OptionsParError where
  pretty err = concat [ concat $ map ppString $ getOptParErrMsgs err
                      , ppString "\n"
                      , ppString helpParMsg
                      ]

-- TODO(ins): rough and ready, fix this
parsePrin ∷ 𝕊 → 𝑂 PrinVal
parsePrin s = case tohs $ list $ splitOn𝕊 "." s of
  [ ρ ]    → Some $ SinglePV ρ
  [ ρ, n ] → Some $ AccessPV ρ $ read𝕊 n
  _        → None

mkParty ∷ 𝑂 𝕊 → PrinVal
mkParty = fromSome ∘ mjoin ∘ map parsePrin

-- TODO(ins): rough and ready, fix this
mkPrg ∷ 𝑂 ℕ → IO Prg
mkPrg = \case
  None      → prgNew
  Some seed → prgFromSeed seed

type Config = 𝐿 (PrinVal ∧ 𝕊)

parsePartyConfig ∷ 𝕊 → 𝑂 (PrinVal ∧ 𝕊)
parsePartyConfig s = case tohs $ list $ splitOn𝕊 "," s of
  [ ρ𝕊 , host ] → do
    ρ    ← parsePrin ρ𝕊
    return $ ρ :* host
  _ → None

parseConfig ∷ 𝕊 → 𝑂 Config
parseConfig s = list ^$ mapM parsePartyConfig $ iter $ splitOn𝕊 ":" s

portOf ∷ ℕ → ℕ → ℕ → ℕ16
portOf n ρ₁ ρ₂ = HS.fromIntegral $ basePort + offset
  where basePort = 12345
        offset   = n × ρ₁ + ρ₂ - gauss
        gauss    = ((ρ₁ + 1) × (ρ₁ + 2)) `HS.div` 2

mkChannel ∷ ℕ → ℕ → 𝕊 → ℕ → 𝕊 → IO Channel
mkChannel n ρMe hostMe ρThem hostThem =
  if ρMe ≡ ρThem then channelNewLocal
  else let iAmServer = ρMe < ρThem in
    if iAmServer then do
      let port = portOf n ρMe ρThem
      channelNewTcpServer hostMe port
    else do
      let port = portOf n ρThem ρMe
      channelNewTcpClient hostThem port

openChannel ∷ 𝐿 PrinVal → PrinVal → 𝕊 → PrinVal → 𝕊 → IO (PrinVal ⇰ Channel)
openChannel parties ρvMe hostMe ρvThem hostThem = (ρvThem ↦) ^$ mkChannel n id₁ hostMe id₂ hostThem
  where n   = count parties
        id₁ = fromSome $ ids ⋕? ρvMe
        id₂ = fromSome $ ids ⋕? ρvThem
        ids = idsFr parties

mkChannels ∷ PrinVal → 𝑂 𝕊 → IO (PrinVal ⇰ Channel)
mkChannels ρvMe s = dict ^$ mapM (\ (ρvThem :* hostThem) → openChannel parties ρvMe hostMe ρvThem hostThem) config
  where parties = map fst config
        config  = fromSome $ mjoin $ map parseConfig s
        hostMe  = fromSome $ (assoc config) ⋕? ρvMe

configPorts ∷ ℕ16 → 𝐿 Port
configPorts n = list $ map ((+) $ HS.fromIntegral 23000) $ upTo n

mkConfigs ∷ 𝑂 𝕊 → (PrinVal ⇰ (Addr ∧ Port))
mkConfigs s = dict $ map (\ ((ρ :* a) :* p) → ρ ↦ (a :* p)) $ fromSome $ zipSameLength config (configPorts n)
  where config = fromSome $ mjoin $ map parseConfig s
        n      = count config

runPar ∷ OptionsPar → 𝐿 𝕊 → IO Doc
runPar opts args = do
  when (optParHelp opts) $ io $ do
    out helpParMsg
    exitIO
  case args of
    path :& Nil → do
      let name = pbasename path
      party    ← return $ mkParty (optParParty opts)
      prg      ← mkPrg (optParSeed opts)
      let configs = mkConfigs (optParConfig opts)
      channels ← mkChannels party (optParConfig opts)
      stdLib   ← io $ parseFile *$ findFile "lib/stdlib.sym"
      program  ← io $ parseFile *$ findFile path
#ifdef PAR
      v ← io $ evalProgram (θ₀ name party prg channels configs) (stdLib ⧺ program)
      return $ pretty v
#else
      io $ out "Symphony compiled without parallel support."
      io $ abortIO
#endif
