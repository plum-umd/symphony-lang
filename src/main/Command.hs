module Command where

import Symphony.Prelude
import qualified Prelude as HS

import Options

import Command.Seq
import Command.Par
import Command.Tc

data Command =
    Seq OptionsSeq
  | Par OptionsPar
  | Tc

parseCommand ∷ 𝐿 𝕊 → Except CommandParseError (Command ∧ 𝐿 𝕊)
parseCommand args = case args of
  cmd :& argsLeft | cmd ≡ "seq" → do
                      opts :* argsLeft ← withExcept SeqParseErr $ parseOptionsSeq argsLeft
                      return $ (Seq opts) :* argsLeft
  cmd :& argsLeft | cmd ≡ "par" → do
                      opts :* argsLeft ← withExcept ParParseErr $ parseOptionsPar argsLeft
                      return $ (Par opts) :* argsLeft
  cmd :& argsLeft | cmd ≡ "tc" → return $ Tc :* argsLeft
  cmd :& _argsLeft → throw $ UnkCmdErr cmd
  Nil              → throw $ NoCmdErr

data CommandParseError =
    NoCmdErr
  | UnkCmdErr 𝕊
  | SeqParseErr OptionsSeqError
  | ParParseErr OptionsParError

instance Pretty CommandParseError where
  pretty parseErr = case parseErr of
    NoCmdErr        → ppString helpMsg
    UnkCmdErr cmd   → concat [ ppErr "No such command:", ppString " ", ppString cmd, ppString "\n\n", ppString helpMsg ]
    SeqParseErr err → pretty err
    ParParseErr err → pretty err

runCommand ∷ Command → 𝐿 𝕊 → ErrorT CommandRunError IO Doc
runCommand cmd args = case cmd of
  Seq opts → withErrorT SeqRunErr $ runSeq opts args
  Par opts → io $ runPar opts args
  Tc       → io $ runTc args

data CommandRunError =
      SeqRunErr SeqRunError

instance Pretty CommandRunError where
  pretty err = case err of
    SeqRunErr err → pretty err
