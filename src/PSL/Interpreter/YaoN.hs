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

instance Protocol 'YaoNP where
  type ProtocolVal 'YaoNP = Ckt

  typeOf ∷ P 'YaoNP → Ckt → BaseType
  typeOf _p = cktType

  shareBaseVal ∷ P 'YaoNP → 𝑃 PrinVal → PrinVal → BaseVal → IM Ckt
  shareBaseVal _p = shareBaseValCkt

  shareUnk ∷ P 'YaoNP → 𝑃 PrinVal → PrinVal → BaseType → IM Ckt
  shareUnk _p = shareUnkCkt

  embedBaseVal ∷ P 'YaoNP → 𝑃 PrinVal → BaseVal → IM Ckt
  embedBaseVal _p = embedBaseValCkt

  exePrim ∷ P 'YaoNP → 𝑃 PrinVal → Op → 𝐿 Ckt → IM Ckt
  exePrim _p = exePrimCkt

  getParty ∷ IM PrinVal
  getParty = do
    lm ← askL iCxtLocalMode        -- Note: Local Mode, `lm`, is always either TopM or a singleton
    ρvs ← fromSome $ view secML lm --   TopM is impossible, since we are in the YaoN protocol (TopM always executes plaintext protocol -- i.e. sequential mode)
    fromSome $ view one𝑃L ρvs      --   ∴ `lm` is a singleton.

  reveal ∷ P 'YaoNP → 𝑃 PrinVal → 𝑃 PrinVal → Ckt → IM BaseVal
  reveal _p ρvs₁ ρvs₂ ckt = do
    let bτ = cktType ckt
    party   ← getParty
    bristol ← cktToBristol ckt
    let cktpath = concat [bristolDir,ppshow party,".txt"]
    io $ fwrite cktpath bristol -- write bristol format circuit to file
    revealed ← runEMP path
    parseBaseType bτ revealed
    where cktToBristol = return ∘ printBCktVal *∘ generateBristol
          bristolDir  = "bristol-circuits/"
          runEMP path = map Text.pack $ io $ Process.readProcess emp [ config,
            Text.unpack path ] []
          emp = Text.unpack "emp-backend"
          parseBaseType bτ str = return $ BoolBV True
