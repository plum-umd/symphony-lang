module Symphony.Dynamic.Par.Error where

import UVMHS

import qualified System.IO.Error as IOE

data IErrorClass =
    SyntaxIError
  | TypeIError
  | NotImplementedIError
  | InternalIError
  deriving (Eq,Ord,Show)

makePrettySum ''IErrorClass

data IError = IError
  { iErrorSource ∷ 𝑂 SrcCxt
  , iErrorCallStack ∷ CallStack
  , iErrorClass ∷ IErrorClass
  , iErrorMsg ∷ Doc
  }

throwIErrorCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIErrorCxt ec em ~vals = withFrozenCallStack $ do
  es ← askL hasLens
  throwIError es ec em vals

throwIError ∷ (Monad m, MonadError IError m, STACK) ⇒ 𝑂 SrcCxt → IErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwIError es ec em vals =
  throw $ IError es callStack ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n,ppString "=",v]
    ]

guardErr ∷ (Monad m, MonadError IError m, STACK) ⇒ Bool -> m () -> m ()
guardErr x im = case x of
  True → skip
  False → im

badCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ m a
badCxt = throwIErrorCxt TypeIError "bad" empty𝐿

todoCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ m a
todoCxt = throwIErrorCxt NotImplementedIError "TODO" empty𝐿

assertCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ 𝔹 → m ()
assertCxt b = guardErr b impossibleCxt

assertM ∷ (Monad m, MonadError IError m, STACK) ⇒ 𝔹 → m ()
assertM b = guardErr b impossibleM

error𝑂 ∷ (Monad m, MonadError IError m, STACK) ⇒ 𝑂 a -> m a -> m a
error𝑂 e er = case e of
  Some x → return x
  None   → er

errorIO ∷ (Monad m, MonadError IError m, MonadIO m, STACK) ⇒ IO a → m a → m a
errorIO xM er = do
  eorx ← io $ map frhs $ IOE.tryIOError xM
  case eorx of
    Inl _ → er
    Inr x → return x

fromSomeM ∷ (Monad m,MonadError IError m, STACK) ⇒ 𝑂 a → m a
fromSomeM x = error𝑂 x impossibleM

fromSomeCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ 𝑂 a → m a
fromSomeCxt x = error𝑂 x impossibleCxt

impossibleM ∷ (Monad m, MonadError IError m, STACK) ⇒ m a
impossibleM = throwIError None InternalIError "Impossible." empty𝐿

impossibleCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError IError m, STACK) ⇒ m a
impossibleCxt = throwIErrorCxt InternalIError "Impossible." empty𝐿
