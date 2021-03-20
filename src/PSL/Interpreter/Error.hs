module PSL.Interpreter.Error where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Lens

-- TODO(ins): some of this can probably go into AddUVMHS, generalized away from IError

throwIErrorCxt ∷ (Monad m,MonadReader ICxt m,MonadError IError m,STACK) ⇒ IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIErrorCxt ec em vals = withFrozenCallStack $ do
  es ← askL iCxtSourceL
  throwIError es ec em vals

throwIError ∷ (Monad m,MonadError IError m,STACK) ⇒ 𝑂 FullContext → IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIError es ec em vals =
  throw $ IError es callStack ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n,ppString "=",v]
    ]

guardErr ∷ (Monad m,MonadError IError m) ⇒ Bool -> m () -> m ()
guardErr x im = case x of
  True → skip
  False → im

error𝑂 ∷ (Monad m,MonadError IError m) ⇒ 𝑂 a -> m a -> m a
error𝑂 e er = case e of
  Some x → return x
  None → er

impossible ∷ IM a
impossible = throwIErrorCxt InternalIError "Impossible." empty𝐿
