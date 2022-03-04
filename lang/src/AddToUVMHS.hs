module AddToUVMHS where

import UVMHS

import qualified Prelude as HS
import qualified Data.Vector.Mutable as VBM
import qualified Data.IORef as IOR

instance (POrd a) ⇒ POrd (AddTop a) where
  _          ⊑ Top        = True
  Top        ⊑ _          = False
  (AddTop a) ⊑ (AddTop b) = a ⊑ b

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

fromSome ∷ 𝑂 a → a
fromSome = \case
  None   → impossible
  Some v → v

find𝐷 ∷ Eq v ⇒ k ⇰ v → v → 𝑂 k
find𝐷 d v = foldOnFrom d None $ \ (k :* v') ok →
  case ok of
    None   → if v ≡ v' then Some k else None
    Some _ → ok

number𝐷 ∷ (Ord a) ⇒ ℕ → 𝑃 a → (a ⇰ ℕ)
number𝐷 init p = let _ :* ds = foldmap init (\ k n → (n + 1) :* (k ↦ n)) p in unionsUniq ds

empty𝑃L ∷ (Ord a, Pretty a) ⇒ 𝑃 a ⌲ ()
empty𝑃L = prism constr destr
  where constr () = pø
        destr  p = case tohs (list p) of
          Nil → Some ()
          _   → None

nonEmpty𝑃L ∷ (Ord a, Pretty a) ⇒ 𝑃 a ⌲ (a ∧ 𝑃 a)
nonEmpty𝑃L = prism constr destr
  where constr (x :* xs) = (single𝑃 x) ∪ xs
        destr = pmin

empty𝐷L ∷ (k ⇰ v) ⌲ ()
empty𝐷L = prism constr destr
  where constr () = dø
        destr d = if isEmpty d then Some () else None

nonEmpty𝐷L ∷ (Ord k) ⇒ (k ⇰ v) ⌲ (k ∧ v ∧ (k ⇰ v))
nonEmpty𝐷L = prism constr destr
  where constr (k :* v :* d) = (k ↦ v) ⩌ d
        destr = dminView

one𝑃L ∷ (Ord a,Pretty a) ⇒ 𝑃 a ⌲ a
one𝑃L = prism constr destr
  where constr x = single x
        destr  p = case tohs (list p) of
          [ x ] → Some x
          _     → None

two𝑃L ∷ (Ord a, Pretty a) ⇒ 𝑃 a ⌲ (a ∧ a)
two𝑃L = prism constr destr
  where constr (x :* y) = pow $ frhs $ [ x, y ]
        destr  p = case tohs (list p) of
          [ x, y ] → Some (x :* y)
          _     → None

nilL ∷ 𝐿 a ⌲ ()
nilL = prism constr destr
  where constr () = Nil
        destr = \case
          Nil → Some ()
          _   → None

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
repeat𝑉 z v = spvec𝐼 $ replicateI z $ \ z' → z' :* v

instance (Pretty a) ⇒ Pretty (𝑉 a) where
  pretty = ppCollection (ppPun "[|") (ppPun "|]") (ppPun ";") ∘ map pretty ∘ iter

impossible ∷ a
impossible = assert False undefined

foldmap ∷ (ToIter a t) ⇒ b → (a → b → b ∧ c) → t → b ∧ 𝐼 c
foldmap init f xs = fold (init :* empty𝐼) thread xs
  where thread x (acc :* r) = let (acc' :* x') = f x acc in acc' :* (snoc𝐼 r x')

foldmapM ∷ (Monad m, ToIter a t) ⇒ b → (a → b → m (b ∧ c)) → t → m (b ∧ 𝐼 c)
foldmapM init f xs = mfold (init :* empty𝐼) thread xs
  where thread x (acc :* r) = do
          (acc' :* x') ← f x acc
          return $ acc' :* (snoc𝐼 r x')

elimℕ ∷ ℕ → (ℕ → a) → 𝐼 a
elimℕ n f = if n ≡ 0 then empty𝐼 else snoc𝐼 (elimℕ (n - 1) f) (f $ n - 1)

choose𝑃 ∷ 𝑃 a → 𝑂 a
choose𝑃 p = map fst $ pmin p

addTopL ∷ (AddTop a) ⌲ a
addTopL = prism constr destr
  where constr x = AddTop x
        destr = \case
          AddTop x → Some x
          Top      → None

idsFr ∷ (Ord a, ToIter a t) ⇒ t → (a ⇰ ℕ)
idsFr xs = dict $ evalState 0 $ mapMOn (iter xs) $ \ x → (x ↦) ^$ next

mapM𝑃 ∷ (Monad m, Ord b) ⇒ (a → m b) → 𝑃 a → m (𝑃 b)
mapM𝑃 f p = pow ^$ mapM f $ iter p

mapMOn𝑃 ∷ (Monad m, Ord b) ⇒ 𝑃 a → (a → m b) → m (𝑃 b)
mapMOn𝑃 = flip mapM𝑃

instance FunctorM 𝑉 where
  mapM f = spvec𝐼 ^∘ mapM (mapMSnd f) ∘ iter

newtype NoEq a = NoEq { unNoEq ∷ a }

instance Eq (NoEq a) where _ == _ = False

new𝕍Mut ∷ ℕ64 → IO (𝕍Mut a)
new𝕍Mut = (map 𝕍Mut) ∘ VBM.new ∘ tohs ∘ intΩ64

length𝕍Mut ∷ 𝕍Mut a → ℕ64
length𝕍Mut v𝕍Mut = natΩ64 $ frhs $ VBM.length $ un𝕍Mut v𝕍Mut

clone𝕍Mut ∷ 𝕍Mut a → IO (𝕍Mut a)
clone𝕍Mut = (map 𝕍Mut) ∘ VBM.clone ∘ un𝕍Mut

map𝕍Mut ∷ (a → a) → 𝕍Mut a → IO ()
map𝕍Mut f a = eachI𝕍Mut f' a
  where f' i x = set𝕍Mut i (f x) a

generateM𝕍Mut ∷ (Monad m, MonadIO m) ⇒ ℕ64 → (ℕ64 → m a) → m (𝕍Mut a)
generateM𝕍Mut n f = do
  v ← io $ new𝕍Mut n
  eachOn (upTo n) $ \ i → do
    xᵢ ← f i
    io $ set𝕍Mut i xᵢ v
  return v

instance Pretty a ⇒ Pretty (𝕍Mut a) where
  pretty v = pretty $ io_UNSAFE $ values𝕍Mut v

newtype ℝMut a = ℝMut { unℝMut ∷ IOR.IORef a }

newℝMut ∷ a → IO (ℝMut a)
newℝMut = (map ℝMut) ∘ IOR.newIORef

readℝMut ∷ ℝMut a → IO a
readℝMut = IOR.readIORef ∘ unℝMut

writeℝMut ∷ ℝMut a → a → IO ()
writeℝMut = IOR.writeIORef ∘ unℝMut

instance Pretty a ⇒ Pretty (ℝMut a) where
  pretty v = pretty $ io_UNSAFE $ readℝMut v

type Cont r a = ContT r ID a

cont ∷ ((a → r) → r) → Cont r a
cont f = ContT $ \ c → ID (f (unID ∘ c))

runCont ∷ Cont r a → (a → r) → r
runCont m k = unID $ runContT (ID ∘ k) m
