module Options where

import Symphony.Prelude
import qualified Prelude as HS

import qualified System.Console.GetOpt as O

data Options = Options
  { optHelp ∷ 𝔹
  , optVersion ∷ 𝔹
  }
makeLenses ''Options

options₀ ∷ Options
options₀ = Options
  { optHelp = False
  , optVersion = False
  }

optionsDescr ∷ 𝐿 (O.OptDescr (Options → Options))
optionsDescr = frhs
  [ O.Option ['h'] [chars "help"]
             (O.NoArg $ update optHelpL True)
           $ chars "show help"
  , O.Option ['v'] [chars "version"]
             (O.NoArg $ update optVersionL True)
           $ chars "print version"
  ]

parseOptions ∷ 𝐿 𝕊 → Except OptionsError (Options ∧ 𝐿 𝕊)
parseOptions args = do
  when isError $ throw $ OptionsError errs
  return $ options :* argsLeft
  where optionsMods :* argsLeft :* errs = Symphony.Prelude.parseOptions optionsDescr args
        isError = not $ isEmpty errs
        options = compose optionsMods options₀

helpMsg ∷ 𝕊
helpMsg = fromChars $ O.usageInfo header $ tohs optionsDescr
  where header = chars $ concat [ "USAGE:\n"
                                , "    symphony [OPTIONS] [COMMAND]\n"
                                , "\n"
                                , "The symphony commands are:\n"
                                , "   seq   Execute a program according to the sequential semantics\n"
                                , "\n"
                                , "See 'symphony <command> --help' for more information on a specific command.\n"
                                , "\n"
                                , "OPTIONS:"
                                ]

data OptionsError = OptionsError { getOptErrMsgs ∷ 𝐿 𝕊 }

instance Pretty OptionsError where
  pretty err = concat [ concat $ map ppString $ getOptErrMsgs err
                      , ppString "\n"
                      , ppString helpMsg
                      ]
