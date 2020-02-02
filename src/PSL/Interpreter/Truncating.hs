module PSL.Interpreter.Truncating where

import UVMHS

import PSL.Syntax

trNat ∷ ℕ → ℕ → ℕ
trNat m n = n ÷ (2 ^^ m)

trPrNat ∷ IPrecision → ℕ → ℕ
trPrNat = \case
  InfIPr → id
  FixedIPr m n → trNat $ m + n

buNat ∷ ℕ → ℕ → ℕ
buNat m n = n + (2 ^^ m)

buPrNat ∷ IPrecision → ℕ → ℕ
buPrNat = \case
  InfIPr → id
  FixedIPr m n → buNat $ m + n

trInt ∷ ℕ → ℤ → ℤ
trInt m i
  | i < neg (int (2 ^^ (m - 1))) = trInt m (i + int (2 ^^ m))
  | i > int (2 ^^ (m - 1) - 1) = trInt m (i - int (2 ^^ m))
  | otherwise = i

trPrInt ∷ IPrecision → ℤ → ℤ
trPrInt = \case
  InfIPr → id
  FixedIPr m n → trInt $ m + n
