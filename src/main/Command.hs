module Command where

import Symphony.Prelude
import qualified Prelude as HS

import Options

import Command.Seq
--import qualified Command.Par as Par

data Command =
    Seq OptionsSeq
--  | Par Par.Options

parseCommand ∷ 𝐿 𝕊 → Except CommandParseError (Command ∧ 𝐿 𝕊)
parseCommand args = case args of
  cmd :& argsLeft | cmd ≡ "seq" → do
                      opts :* argsLeft ← withExcept SeqParseErr $ parseOptionsSeq argsLeft
                      return $ (Seq opts) :* argsLeft
--  cmd :& argsLeft | cmd ≡ "par" → do
--                      opts ← Par.parseOptions
--                      return $ Par opts
  cmd :& _argsLeft → throw $ UnkCmdErr cmd
  Nil              → throw $ NoCmdErr

data CommandParseError =
    NoCmdErr
  | UnkCmdErr 𝕊
  | SeqParseErr OptionsSeqError

instance Pretty CommandParseError where
  pretty parseErr = case parseErr of
    NoCmdErr        → ppString helpMsg
    UnkCmdErr cmd   → concat [ ppErr "No such command:", ppString " ", ppString cmd, ppString "\n\n", ppString helpMsg ]
    SeqParseErr err → pretty err

runCommand ∷ Command → 𝐿 𝕊 → ErrorT CommandRunError IO Doc
runCommand cmd args = case cmd of
  Seq opts → withErrorT SeqRunErr $ runSeq opts args

data CommandRunError =
    SeqRunErr SeqRunError

instance Pretty CommandRunError where
  pretty err = case err of
    SeqRunErr err → pretty err
