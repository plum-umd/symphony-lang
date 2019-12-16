module PSL.Data.Fix where

import UVMHS

-- newtype Fix f = Fix { unFix ∷ f (Fix f) }
-- makePrettyUnion ''Fix
-- deriving instance (∀ a. Eq a ⇒ Eq (f a)) ⇒ Eq (Fix f)
-- deriving instance (∀ a. Eq a ⇒ Eq (f a),∀ a. Ord a ⇒ Ord (f a)) ⇒ Ord (Fix f)
-- deriving instance (∀ a. Show a ⇒ Show (f a)) ⇒ Show (Fix f)
-- 
-- newtype AFix t f = AFix { unAFix ∷ f (Annotated t (AFix t f)) }
-- deriving instance (∀ a. Eq a ⇒ Eq (f (Annotated t a))) ⇒ Eq (AFix t f)
-- deriving instance (∀ a. Eq a ⇒ Eq (f (Annotated t a)),∀ a. Ord a ⇒ Ord (f (Annotated t a))) ⇒ Ord (AFix t f)
-- deriving instance (∀ a. Show a ⇒ Show (f (Annotated t a))) ⇒ Show (AFix t f)
-- makePrettyUnion ''AFix
-- 
-- stripAFix ∷ (Functor f) ⇒ AFix t f → Fix f
-- stripAFix = Fix ∘ map (stripAFix ∘ extract) ∘ unAFix
