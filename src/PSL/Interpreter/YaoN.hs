module PSL.Interpreter.YaoN where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import PSL.Interpreter.Circuits

import qualified Data.Text as Text
import qualified System.Process as Process
import qualified Prelude as HS

instance Protocol 'YaoNP where
  type ProtocolVal 'YaoNP = Ckt

  typeOf ∷ P 'YaoNP → Ckt → BaseType
  typeOf _p = cktType

  shareBaseVal ∷ P 'YaoNP → PrinVal → BaseVal → IM Ckt
  shareBaseVal _p = shareBaseValCkt

  shareUnk ∷ P 'YaoNP → PrinVal → BaseType → IM Ckt
  shareUnk _p = shareUnkCkt

  embedBaseVal ∷ P 'YaoNP → BaseVal → IM Ckt
  embedBaseVal _p = embedBaseValCkt

  exePrim ∷ P 'YaoNP → Op → 𝐿 Ckt → IM Ckt
  exePrim _p = exePrimCkt

  reveal ∷ P 'YaoNP → 𝑃 PrinVal → Ckt → IM BaseVal
  reveal _p ρvs ckt = do
    src ← fromSome *$ askL iCxtSourceL
    pptraceM src
    ρv ← fromSome *$ map (view one𝑃L) $ fromSome *$ map (view secML) $ askL iCxtLocalModeL
    bristol ← cktToBristol ckt
    party ← case ρv of
              SinglePV ρ → return ρ
              _ → throwIErrorCxt NotImplementedIError "not implemented" empty𝐿
    let path = concat ["bristol-circuits/",party,".txt"]
    io $ fwrite path bristol -- TODO: check if directory exists, if not then create it
    result ← map Text.pack $ io $ Process.readProcess emp [ Text.unpack path ] []
    pptraceM result
    return $ BoolBV True
    where emp            = Text.unpack "cat"
          cktToBristol _ = return $ Text.pack $ HS.unlines $ map Text.unpack [ "1 3", "2 1 1", "1 1", "", "2 1 0 1 2 AND" ]
