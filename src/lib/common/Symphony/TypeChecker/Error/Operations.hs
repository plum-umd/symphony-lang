module Symphony.TypeChecker.Error.Operations where

import UVMHS

import Symphony.TypeChecker.Error.Types

-- Format an error message and arguments
formatMsg ∷ 𝕊 → 𝐿 (𝕊 ∧ Doc) → Doc
formatMsg s vs = ppVertical
                 [ ppString s
                 , ppVertical $ mapOn vs $ \ (n :* v) → ppHorizontal [ ppString n, ppString "=", v ]
                 ]

-- Print an error
printError ∷ Error → IO ()
printError (Error rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

-- Throw an `Error`
throwError ∷ (Monad m, MonadError Error m, STACK) ⇒ 𝑂 SrcCxt → Class → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwError es ec em evs = throw e
  where e = Error
            { teSource    = es
            , teCallStack = callStack
            , teClass     = ec
            , teMsg       = formatMsg em evs
            }

-- Throw an `Error`, where source location comes from Reader
throwErrorCxt ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError Error m, STACK) ⇒ Class → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwErrorCxt ec em evs = do
  es ← askL hasLens
  throwError es ec em evs

-- Throw a type error with message
typeError ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError Error m, STACK) ⇒ 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
typeError em evs = throwErrorCxt TypeError em evs

-- TODO
todoError ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError Error m, STACK) ⇒ m a
todoError = throwErrorCxt NotImplementedError "TODO" empty𝐿

-- IMPOSSIBLE
impossibleError ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError Error m, STACK) ⇒ m a
impossibleError = throwErrorCxt InternalError "(apparently not) IMPOSSIBLE" empty𝐿

-----------------
-- Convenience --
-----------------

guardErr ∷ (Monad m, MonadError Error m, STACK) ⇒ Bool → m () → m ()
guardErr g c = if g then skip else c

fromSome ∷ (Monad m, MonadReader c m, HasLens c (𝑂 SrcCxt), MonadError Error m, STACK) ⇒ 𝑂 a → m a
fromSome vO = case vO of
  None   → impossibleError
  Some v → return v
