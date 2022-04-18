module Symphony.TypeChecker.Types where

import UVMHS

import Symphony.Lang.Syntax

----------------------------
-- Typing Environment (Γ) --
----------------------------

type TEnv = 𝕏 ⇰ Type

-------------
-- Context --
-------------

data TCxt = TCxt
  { tCxtSource ∷ 𝑂 SrcCxt
  , tCxtEnv ∷ TEnv
  } deriving (Eq, Ord, Show)

instance Null TCxt where
  null = TCxt { tCxtSource = None, tCxtEnv = null }

------------
-- Errors --
------------

data TErrorClass =
    TypeTError
  | NotImplementedTError
  | InternalTError
  deriving (Eq, Ord, Show)

data TError = TError
  { tErrorSource    ∷ 𝑂 SrcCxt
  , tErrorCallStack ∷ CallStack
  , tErrorClass     ∷ TErrorClass
  , tErrorMsg       ∷ Doc
  }

printError ∷ TError → IO ()
printError (TError rsO cs rc rm) = pprint $ ppVertical $ concat
  [ single𝐼 $ ppHeader $ show𝕊 rc
  , elim𝑂 empty𝐼 (single𝐼 ∘ pretty) rsO
  , single𝐼 $ rm
  , single𝐼 $ pretty cs
  ]

throwTErrorCxt ∷ (Monad m, MonadReader r m, HasLens r (𝑂 SrcCxt), MonadError TError m, STACK) ⇒ TErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwTErrorCxt ec em vals = withFrozenCallStack $ do
  es ← askL hasLens
  throwTError es ec em vals

throwTError ∷ (Monad m, MonadError TError m, STACK) ⇒ 𝑂 SrcCxt → TErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwTError es ec em vals =
  throw $ TError es callStack ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n, ppString "=",v]
    ]

----------------
-- TYPE MONAD --
----------------

newtype TM a = TM { unTM ∷ ReaderT TCxt (ErrorT TError ID) a }
  deriving
  ( Functor
  , Return, Bind, Monad
  , MonadReader TCxt
  , MonadError TError
  )

runTM ∷ TCxt → TM a → (TError ∨ a)
runTM cxt = unID ∘ unErrorT ∘ (runReaderT cxt) ∘ unTM

runTMIO ∷ TCxt → 𝕊 → TM a → IO a
runTMIO cxt name xM = case runTM cxt xM of
  Inr x → return x
  Inl e → do
    pprint $ ppHorizontal [ ppErr ">", ppBD $ ppString name ]
    printError e
    abortIO

makeLenses ''TCxt

instance HasLens TCxt (𝑂 SrcCxt) where
  hasLens = tCxtSourceL
