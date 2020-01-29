module PSL.Data.Mode where

import UVMHS

import PSL.Syntax

data Mode =
    BotM
  | SecM PrinVal
  | SSecM (𝑃 PrinVal)
  | TopM
  deriving (Eq,Ord,Show)
makePrettySum ''Mode

instance Top Mode where top = TopM
instance Bot Mode where bot = BotM
instance Join Mode where
  BotM ⊔ m = m
  m ⊔ BotM = m
  TopM ⊔ _ = TopM
  _ ⊔ TopM = TopM
  SecM ρ₁ ⊔ SecM ρ₂
    | ρ₁ ≡ ρ₂ = SecM ρ₁
    | otherwise = SSecM $ pow [ρ₁,ρ₂]
  SecM ρ₁ ⊔ SSecM ρs₂ = SSecM $ single ρ₁ ∪ ρs₂
  SSecM ρs₁ ⊔ SecM ρ₂ = SSecM $ ρs₁ ∪ single ρ₂
  SSecM ρs₁ ⊔ SSecM ρs₂ = SSecM $ ρs₁ ∪ ρs₂
instance Meet Mode where
  BotM ⊓ _ = BotM
  _ ⊓ BotM = BotM
  TopM ⊓ m = m
  m ⊓ TopM = m
  SecM ρ₁ ⊓ SecM ρ₂
    | ρ₁ ≡ ρ₂ = SecM ρ₁
    | otherwise = BotM
  SecM ρ₁ ⊓ SSecM ρs₂ = SSecM $ single ρ₁ ⊓ ρs₂
  SSecM ρs₁ ⊓ SecM ρ₂ = SSecM $ ρs₁ ⊓ single ρ₂
  SSecM ρs₁ ⊓ SSecM ρs₂ = SSecM $ ρs₁ ∩ ρs₂
instance JoinLattice Mode
instance MeetLattice Mode
instance Lattice Mode

instance POrd Mode where 
  BotM ⊑ _ = True
  _ ⊑ BotM = False
  _ ⊑ TopM = True
  TopM ⊑ _ = False
  SecM ρ₁ ⊑ SecM ρ₂ = ρ₁ ≡ ρ₂
  SecM ρ₁ ⊑ SSecM ρs₂ = ρ₁ ∈ ρs₂
  SSecM ρs₁ ⊑ SecM ρ₂ = ρs₁ ⊆ single ρ₂
  SSecM ρs₁ ⊑ SSecM ρs₂ = ρs₁ ⊆ ρs₂
