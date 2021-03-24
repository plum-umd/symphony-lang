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

  exeBaseVal ∷ P 'PlainP → 𝑂 PrinVal → BaseVal → IM BaseVal
  exeBaseVal _p _ρv bv = return bv

  exeUnk ∷ P 'PlainP → PrinVal → BaseType → IM BaseVal
  exeUnk _p ρv bτ = throwIErrorCxt NotImplementedIError "[PlainP] exeUnk: TODO" empty𝐿

  exePrim ∷ P 'PlainP → Op → 𝐿 BaseVal → IM BaseVal
  exePrim _p = interpPrim

  reveal ∷ P 'PlainP → 𝑃 PrinVal → BaseVal → IM BaseVal
  reveal _p _ρvs = return
