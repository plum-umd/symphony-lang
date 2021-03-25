module PSL.Interpreter.Plain where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Error
import PSL.Interpreter.Primitives
import PSL.Interpreter.Pretty ()

instance Protocol 'PlainP where
  type ProtocolVal 'PlainP = BaseVal

  typeOf ∷ P 'PlainP → BaseVal → BaseType
  typeOf _p = typeOfBaseVal

  shareBaseVal ∷ P 'PlainP → PrinVal → BaseVal → IM BaseVal
  shareBaseVal _p _ρv = return

  shareUnk ∷ P 'PlainP → PrinVal → BaseType → IM BaseVal
  shareUnk _p ρv bτ = throwIErrorCxt NotImplementedIError "[PlainP] exeUnk: TODO" empty𝐿

  embedBaseVal ∷ P 'PlainP → BaseVal → IM BaseVal
  embedBaseVal _p = return

  exePrim ∷ P 'PlainP → Op → 𝐿 BaseVal → IM BaseVal
  exePrim _p = interpPrim

  reveal ∷ P 'PlainP → 𝑃 PrinVal → BaseVal → IM BaseVal
  reveal _p _ρvs = return
