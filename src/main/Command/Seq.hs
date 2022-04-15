module Command.Seq where

import Symphony.Prelude
import qualified Prelude as HS

import Options

import Symphony.Lang.Parser
import Symphony.Dynamic.Seq
import Symphony.Dynamic.Seq.Types

import qualified System.Console.GetOpt as O
import qualified Crypto.Random as R

data OptionsSeq = OptionsSeq
  { optSeqHelp ∷ 𝔹
  , optSeqSeed ∷ 𝑂 ℕ
  }
makeLenses ''OptionsSeq

optionsSeq₀ ∷ OptionsSeq
optionsSeq₀ = OptionsSeq
  { optSeqHelp = False
  , optSeqSeed = None
  }

optionsSeqDescr ∷ 𝐿 (O.OptDescr (OptionsSeq → OptionsSeq))
optionsSeqDescr = frhs
  [ O.Option ['h'] [chars "help"]
             (O.NoArg $ update optSeqHelpL True)
           $ chars "show help"
  , O.Option ['s'] [chars "seed"]
             (O.ReqArg (\ s → update optSeqSeedL $ Some $ HS.read s) $ chars "NAT")
           $ chars "set random seed"
  ]

parseOptionsSeq ∷ 𝐿 𝕊 → Except OptionsSeqError (OptionsSeq ∧ 𝐿 𝕊)
parseOptionsSeq args = do
  when isError $ throw (OptionsSeqError errs)
  return $ options :* argsLeft
  where optionsMods :* argsLeft :* errs = Symphony.Prelude.parseOptions optionsSeqDescr args
        isError = not $ isEmpty errs
        options = compose optionsMods optionsSeq₀

helpSeqMsg ∷ 𝕊
helpSeqMsg = fromChars $ O.usageInfo header $ tohs optionsSeqDescr
  where header = chars $ concat [ "USAGE:\n"
                                , "    symphony seq [OPTIONS] <PATH> [PATH]...\n"
                                , "\n"
                                , "OPTIONS:"
                                ]

data OptionsSeqError = OptionsSeqError { getOptSeqErrMsgs ∷ 𝐿 𝕊 }

instance Pretty OptionsSeqError where
  pretty err = concat [ concat $ map ppString $ getOptSeqErrMsgs err
                      , ppString "\n"
                      , ppString helpSeqMsg
                      ]

runSeq ∷ OptionsSeq → 𝐿 𝕊 → ErrorT SeqRunError IO Doc
runSeq opts args = do
  when (optSeqHelp opts) $ io $ do
    out helpSeqMsg
    exitIO
  program ← io $ map concat $ mapM parseFile args
  prg ← io $ case optSeqSeed opts of
               None      → R.drgNew
               Some seed → return $ R.drgNewSeed $ R.seedFromInteger $ HS.fromIntegral seed
  v ← io $ evalProgram θ₀ (ωtl₀ prg) program
  return $ pretty v

type SeqRunError = ()
