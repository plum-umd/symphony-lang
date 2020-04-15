module AddToUVMHS where

import UVMHS

-- ====== --
-- AddBTD --
-- ====== --

data AddBTD a = BotBTD | TopBTD | AddBTD a
  deriving (Eq,Ord,Show)

instance Bot (AddBTD a) where 
  -- {-# INLINE bot #-}
  bot = BotBTD
instance (Eq a) ⇒ Join (AddBTD a) where
  -- {-# INLINE (⊔) #-}
  BotBTD ⊔ x = x
  x ⊔ BotBTD = x
  TopBTD ⊔ _ = TopBTD
  _ ⊔ TopBTD = TopBTD
  AddBTD x ⊔ AddBTD y 
    | x ≡ y = AddBTD x
    | otherwise = TopBTD
instance Top (AddBTD a) where 
  -- {-# INLINE top #-}
  top = TopBTD
instance (Eq a) ⇒ Meet (AddBTD a) where
  -- {-# INLINE (⊓) #-}
  BotBTD ⊓ _ = BotBTD
  _ ⊓ BotBTD = BotBTD
  TopBTD ⊓ x = x
  x ⊓ TopBTD = x
  AddBTD x ⊓ AddBTD y 
    | x ≡ y = AddBTD x
    | otherwise = BotBTD
instance (Eq a) ⇒ JoinLattice (AddBTD a)
instance (Eq a) ⇒ MeetLattice (AddBTD a)
instance (Eq a) ⇒ Lattice (AddBTD a)
instance Functor AddBTD where 
  -- {-# INLINE map #-}
  map = mmap
instance Return AddBTD where 
  -- {-# INLINE return #-}
  return = AddBTD
instance Bind AddBTD where 
  -- {-# INLINE (≫=) #-}
  xM ≫= f = case xM of {TopBTD → TopBTD;BotBTD → BotBTD;AddBTD x → f x}
instance Monad AddBTD
instance FunctorM AddBTD where 
  -- {-# INLINE mapM #-}
  mapM f xM = case xM of {TopBTD → return TopBTD;BotBTD → return BotBTD;AddBTD x → map AddBTD $ f x}

instance (Pretty a) ⇒ Pretty (AddBTD a) where
  pretty BotBTD = ppCon "⊥"
  pretty TopBTD = ppCon "⊤"
  pretty (AddBTD x) = pretty x
