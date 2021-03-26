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

  shareBaseVal ∷ P 'PlainP → 𝑃 PrinVal → PrinVal → BaseVal → IM BaseVal
  shareBaseVal _p _ρvs _ρv = return

  shareUnk ∷ P 'PlainP → 𝑃 PrinVal → PrinVal → BaseType → IM BaseVal
  shareUnk _p _ρvs _ρv _bτ = throwIErrorCxt NotImplementedIError "[PlainP] exeUnk: TODO" empty𝐿

  embedBaseVal ∷ P 'PlainP → 𝑃 PrinVal → BaseVal → IM BaseVal
  embedBaseVal _p _ρvs = return

  exePrim ∷ P 'PlainP → 𝑃 PrinVal → Op → 𝐿 BaseVal → IM BaseVal
  exePrim _p _ρvs = interpPrim

  reveal ∷ P 'PlainP → 𝑃 PrinVal → 𝑃 PrinVal → BaseVal → IM BaseVal
  reveal _p _ρvs₁ _ρvs₂ = return
