module PSL.Interpreter.YaoN where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import PSL.Interpreter.Circuits
import PSL.Interpreter.Bristol

import qualified Data.Text as Text
import qualified System.Process as Process

getParty ∷ IM PrinVal
getParty = do
  lm ← askL iCxtLocalModeL       -- Note: Local Mode, `lm`, is always either TopM or a singleton
  ρvs ← fromSome $ view secML lm --   TopM is impossible, since we are in the YaoN protocol (TopM always executes plaintext protocol -- i.e. sequential mode)
  fromSome $ view one𝑃L ρvs      --   ∴ `lm` is a singleton.

instance Protocol 'YaoNP where
  type ProtocolVal 'YaoNP = Ckt

  typeOf ∷ P 'YaoNP → Ckt → BaseType
  typeOf _p = cktType

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → PrinVal → BaseVal → m Ckt
  shareBaseVal _p = shareBaseValCkt

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → PrinVal → BaseType → m Ckt
  shareUnk _p = shareUnkCkt

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → BaseVal → m Ckt
  embedBaseVal _p = embedBaseValCkt

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → Op → 𝐿 Ckt → m Ckt
  exePrim _p = exePrimCkt

  reveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → 𝑃 PrinVal → MPCVal 'YaoNP → m Val
  reveal _p ρvs₁ ρvs₂ v̂ = do
    pptraceM v̂
    bristol ← bristolFrMPCVal v̂
--    pptraceM bristol
    return $ BaseV $ BoolBV True
{-
    do
    let bτ = mpcValType v̂
    party   ← getParty
    bristol ← cktToBristol ckt
    let cktPath = concat [bristolDir,ppshow party,".txt"]
    io $ fwrite cktPath bristol
    revealed ← runEMP "" party ""
    return $ BoolBV True
    where cktToBristol = return ∘ printBCktVal *∘ generateBristol
          runEMP configPath party input = map Text.pack $ io $ Process.readProcess emp [ Text.unpack configPath, Text.unpack $ show𝕊 party ] $ Text.unpack input
          emp = Text.unpack "emp-backend"
          bristolDir   = "bristol-circuits/" -}
