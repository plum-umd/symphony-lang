module AddToUVMHS where

import UVMHS

import qualified Prelude as HS

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

data DEq a b where
  YesDEq ∷ (a ~ b) ⇒ DEq a b
  NoDEq ∷ DEq a b

data DCmp a b where
  LTDCmp ∷ DCmp a b
  EQDCmp ∷ (a ~ b) ⇒ DCmp a b
  GTDCmp ∷ DCmp a b

class DEqable (a ∷ k → ★) where
  deq ∷ (a b) → (a c) → DEq b c

class DCmpable (a ∷ k → ★) where
  dcmp ∷ (a b) → (a c) → DCmp b c

logBase ∷ 𝔻 → 𝔻 → 𝔻
logBase = HS.logBase

impLookup𝐷 ∷ Ord k ⇒ (k ⇰ v) → k → v
impLookup𝐷 d k =
  case lookup𝐷 d k of
    None   → impossible
    Some v → v

(⩌!) ∷ Ord k ⇒ (k ⇰ v) → (k ⇰ v) → k ⇰ v
d₁ ⩌! d₂ = unionWith (\ _ _ → impossible) d₁ d₂

unionsUniq ∷ (Ord k, ToIter (k ⇰ v) t) => t -> k ⇰ v
unionsUniq = unionsWith (\ _ _ → impossible)

impFromSome ∷ 𝑂 a → a
impFromSome = \case
  None   → impossible
  Some v → v

find𝐷 ∷ Eq v ⇒ k ⇰ v → v → 𝑂 k
find𝐷 d v = foldOnFrom d None $ \ (k :* v') ok →
  case ok of
    None   → if v ≡ v' then Some k else None
    Some _ → ok

mapM𝐷 ∷ (Ord k,Monad m) ⇒ (a → m b) → (k ⇰ a) → m (k ⇰ b)
mapM𝐷 f d = mapM (mapM f) (iter d) ≫= return ∘ dict𝐼

instance Ord k ⇒ FunctorM ((⇰) k) where
  mapM = mapM𝐷

one𝑃L ∷ (Ord a) ⇒ 𝑃 a ⌲ a
one𝑃L = prism constr destr
  where constr x = single x
        destr  p = map fst $ pmin p

one𝐿L ∷ 𝐿 a ⌲ a
one𝐿L = prism constr destr
  where constr x = frhs [ x ]
        destr = \case
          x :& Nil → Some x
          _ → None

two𝐿L ∷ 𝐿 a ⌲ a ∧ a
two𝐿L = prism constr destr
  where constr (x :* y) = frhs [ x, y ]
        destr = \case
          x :& y :& Nil → Some $ x :* y
          _ → None

three𝐿L ∷ 𝐿 a ⌲ a ∧ a ∧ a
three𝐿L = prism constr destr
  where constr (x :* y :* z) = frhs [ x, y, z ]
        destr = \case
          x :& y :& z :& Nil → Some $ x :* y :* z
          _ → None

repeat𝑉 ∷ ℤ64 → a → 𝑉 a
repeat𝑉 z v = spvec𝐼 $ repeatI z $ \ z' → z' :* v

instance (Pretty a) ⇒ Pretty (𝑉 a) where
  pretty = ppCollection (ppPun "[|") (ppPun "|]") (ppPun ";") ∘ map pretty ∘ iter

impossible ∷ a
impossible = assert False undefined

foldmapM ∷ (Monad m, ToIter a t) ⇒ b → (a → b → m (b ∧ c)) → t → m (b ∧ 𝐼 c)
foldmapM init f xs = mfold (init :* empty𝐼) thread xs
  where thread x (acc :* r) = do
          (acc' :* x') ← f x acc
          return $ acc' :* (snoc𝐼 r x')
