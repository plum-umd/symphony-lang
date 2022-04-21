module Command.Par where

import Symphony.Prelude
import qualified Prelude as HS

import Options

import Symphony.Lang.Syntax
import Symphony.Lang.Parser
-- TODO(ins): Should remove CPP here and instead add stub module for Par to Symphony library
#ifdef PAR
import Symphony.Dynamic.Par
import Symphony.Dynamic.Par.Types
#endif

import qualified System.Console.GetOpt as O
import qualified Crypto.Random as R

data OptionsPar = OptionsPar
  { optParHelp  ∷ 𝔹
  , optParSeed  ∷ 𝑂 ℕ
  }
makeLenses ''OptionsPar

optionsPar₀ ∷ OptionsPar
optionsPar₀ = OptionsPar
  { optParHelp  = False
  , optParSeed  = None
  }

optionsParDescr ∷ 𝐿 (O.OptDescr (OptionsPar → OptionsPar))
optionsParDescr = frhs
  [ O.Option ['h'] [chars "help"]
             (O.NoArg $ update optParHelpL True)
           $ chars "show help"
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
                                , "    symphony seq [OPTIONS] <PARTY> <PATH> [PATH]...\n"
                                , "\n"
                                , "OPTIONS:"
                                ]

data OptionsParError = OptionsParError { getOptParErrMsgs ∷ 𝐿 𝕊 }

instance Pretty OptionsParError where
  pretty err = concat [ concat $ map ppString $ getOptParErrMsgs err
                      , ppString "\n"
                      , ppString helpParMsg
                      ]

-- TODO(ins): rough and ready
parseParty ∷ 𝕊 → 𝑂 PrinVal
parseParty s = case list $ splitOn𝕊 "." s of
  ρ :& Nil      → Some $ SinglePV ρ
  ρ :& n :& Nil → Some $ AccessPV ρ (read𝕊 n)
  _             → None

-- TODO(ins): rough and ready
parsePartyIO ∷ 𝕊 → IO PrinVal
parsePartyIO s = case parseParty s of
  None → do
    out $ concat [ "Couldn't parse <PARTY>: ", s ]
    abortIO
  Some ρv → return ρv

runPar ∷ OptionsPar → 𝐿 𝕊 → ErrorT ParRunError IO Doc
runPar opts args = do
  when (optParHelp opts) $ io $ do
    out helpParMsg
    exitIO
  case args of
    me :& argsLeft → do
      program ← io $ map concat $ mapM parseFile argsLeft
      prg ← io $ case optParSeed opts of
               None      → R.drgNew
               Some seed → return $ R.drgNewSeed $ R.seedFromInteger $ HS.fromIntegral seed
      ρvMe ← io $ parsePartyIO me
#ifdef PAR
      v ← io $ evalProgram (θ₀ ρvMe) (ωtl₀ prg) evalProgram
      return $ pretty v
#else
      io $ out "Symphony compiled without parallel support."
      io $ abortIO
#endif

type ParRunError = ()
