module PSL.Interpreter.Access where

import UVMHS
import AddToUVMHS

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Json ()
import PSL.Interpreter.Primitives
import PSL.Interpreter.Share
import PSL.Interpreter.Val

-- enter a strictly smaller mode than the current one
restrictMode ∷ (STACK) ⇒ Mode → IM a → IM a
restrictMode m' xM = do
  m ← askL iCxtGlobalModeL
  let m'' = m ⊓ m'
  guardErr (m'' ≢ SecM pø) (throwIErrorCxt TypeIError "m ⊓ m' ≡ ∅" $ frhs
    [ ("m",pretty m)
    , ("m'",pretty m')
    ])
  localL iCxtGlobalModeL m'' xM
