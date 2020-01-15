module PSL.Data.Mode where

import UVMHS

import PSL.Syntax

data Mode =
    TopM
  | SecM PrinExp
  | SSecM (𝑃 PrinExp)
  | BotM
  deriving (Eq,Ord,Show)
makePrettySum ''Mode

instance Top Mode where top = TopM
instance Bot Mode where bot = BotM
instance Join Mode where
  m₁ ⊔ m₂ | m₁ ≡ m₂ = m₁
  BotM ⊔ m = m
  m ⊔ BotM = m
  SSecM ps₁ ⊔ SSecM ps₂ = SSecM $ ps₁ ∪ ps₂
  _ ⊔ _ = TopM
instance Meet Mode where
  m₁ ⊓ m₂ | m₁ ≡ m₂ = m₁
  TopM ⊓ m = m
  m ⊓ TopM = m
  SSecM ps₁ ⊓ SSecM ps₂ = SSecM $ ps₁ ∩ ps₂
  _ ⊓ _ = BotM
instance JoinLattice Mode
instance MeetLattice Mode
instance Lattice Mode

instance POrd Mode where m₁ ⊑ m₂ = (m₁ ⊔ m₂) ≡ m₂


