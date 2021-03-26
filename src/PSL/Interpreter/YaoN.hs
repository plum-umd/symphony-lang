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
import qualified Prelude as HS

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

  reveal ∷ P 'YaoNP → 𝑃 PrinVal → 𝑃 PrinVal → Ckt → IM BaseVal
  reveal _p ρvs₁ ρvs₂ ckt = do
    src ← fromSome *$ askL iCxtSourceL
    let lr = fullContextLocRange src
    pptraceM $ show𝕊 lr
    let bτ = cktType ckt
    party   ← getParty
    bristol ← cktToBristol ckt
    let path = concat [bristolDir,party,".txt"]
    io $ fwrite path bristol -- write bristol format circuit to file
    revealed ← runEMP path
    parseBaseType bτ revealed
    where getParty = do
            lm  ← askL iCxtLocalModeL
            ρvs ← fromSome $ view secML lm
            ρv  ← fromSome $ view one𝑃L ρvs
            case ρv of
              SinglePV ρ   → return ρ
              AccessPV s i → return $ s ⧺ "_" ⧺ show𝕊 i
              VirtualPV s  → impossible
          cktToBristol ckt' = do
            bcv ← generateBristol ckt'
            return $ printBCktVal bcv
          bristolDir  = "bristol-circuits/"
          runEMP path = map Text.pack $ io $ Process.readProcess emp [ Text.unpack path ] []
          emp = Text.unpack "cat"
          parseBaseType bτ str = return $ BoolBV True
