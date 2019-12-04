module PSL.TypeChecker where

import UVMHS

import PSL.Syntax
import PSL.Common

-- Γ ∈ env
type TEnv = 𝕏 ⇰ Type

-- Ξ ∈ tcxt
data TCxt = TCxt
  { tCxtEnv ∷ TEnv
  , tCxtDecl ∷ TEnv
  , tCxtMode ∷ Mode
  } deriving (Eq,Ord,Show)
makePrettySum ''TCxt

-- η ∈ effect
data TEff = TEff
  { tEffInp ∷ 𝑃 Prin
  , tEffRev ∷ 𝑃 Prin
  } deriving (Eq,Ord,Show)
makePrettySum ''TEff

newtype TM a = TM { unTM ∷ RWS TCxt () () a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader TCxt
  ,MonadWriter ()
  ,MonadState ()
  )
makePrettySum ''TM

elabExpInfer ∷ AExp → TM (AExp ∧ Type)
elabExpInfer eA = case extract eA of
  _ → undefined

elabExpCheck ∷ AExp → Type → TM AExp 
elabExpCheck eA τ = case extract eA of
  _ → undefined

testTypeChecker ∷ IO ()
testTypeChecker = return ()

