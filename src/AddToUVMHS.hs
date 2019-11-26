module AddToUVMHS where

import UVMHS

cpNatural ∷ CParser TokenBasic ℕ
cpNatural = do
  i ← cpInteger
  case natO i of
    Some n → return n
    None → abort

cpManyContext ∷ (Ord t,Comonad f) ⇒ (∀ b. CParser t b → CParser t (f b)) → CParser t a → CParser t (𝐿 (f a))
cpManyContext f xM = tries
  [ cpOneOrMoreContext f xM
  , return Nil
  ]

cpOneOrMoreContext ∷ (Ord t,Comonad f) ⇒ (∀ b. CParser t b → CParser t (f b)) → CParser t a → CParser t (𝐿 (f a))
cpOneOrMoreContext f xM = do
  xxs ← f $ do
    x ← xM
    xs ← cpManyContext f xM
    return $ x :* xs
  let x :* xs = extract xxs
  return $ siphon xxs x :& xs

cpManySepByContext ∷ (Ord t,Comonad f) ⇒ (∀ b. CParser t b → CParser t (f b)) → CParser t () → CParser t a → CParser t (𝐿 (f a))
cpManySepByContext f sepM xM = tries
  [ cpOneOrMoreSepByContext f sepM xM
  , return Nil
  ]

cpOneOrMoreSepByContext ∷ (Ord t,Comonad f) ⇒ (∀ b. CParser t b → CParser t (f b)) → CParser t () → CParser t a → CParser t (𝐿 (f a))
cpOneOrMoreSepByContext f sepM xM = do
  xxs ← f $ do
    x ← xM
    xs ← cpManyContext f $ map snd $ sepM ⧆ xM
    return $ x :* xs
  let x :* xs = extract xxs
  return $ siphon xxs x :& xs

cpNewWithContextRendered ∷ (Ord t) ⇒ 𝕊 → CParser t a → CParser t (Annotated FullContext a)
cpNewWithContextRendered s = cpNewContext s ∘ cpWithContextRendered
