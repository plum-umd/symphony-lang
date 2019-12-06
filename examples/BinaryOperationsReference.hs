module BinaryOperationsReference where

import Data.Word

xor :: Bool -> Bool -> Bool
xor False a = a
xor True a = not a

-- For concreteness, each N has a 32 bit representation.
-- For simplicity, we just use lists rather than some dependent vector representation.
newtype N = N { getN :: [Bool] }

wordToN :: Word32 -> N
wordToN = N . loop 32
  where
    loop 0 _ = []
    loop n a =
      let (r, q) = a `divMod` 2
       in (q == 1) : loop (n-1) r

nToWord :: N -> Word32
nToWord (N xs) = loop xs
  where
    loop [] = 0
    loop (x:xs) = (if x then 1 else 0) + (2 * loop xs)

instance Show N where
  show = show . nToWord

-- Correctness: nToWord . wordToN = id
translationCorrect :: Word32 -> Bool
translationCorrect x = nToWord (wordToN x) == x

binEq :: N -> N -> Bool
binEq (N xs) (N ys) = xs == ys

-- Correctness: forall x, y :: Word32. (wordToN x `binEq` wordToN y) = x == y
eqCorrect :: Word32 -> Word32 -> Bool
eqCorrect x y = (wordToN x `binEq` wordToN y) == (x == y)

instance Eq N where
  (==) = binEq

binLt :: N -> N -> Bool
binLt (N as) (N bs) = loop as bs
  where
    loop [] [] = False
    loop (a:as) (b:bs) = loop as bs || (as == bs && (not a && b))

-- Correctness: forall x, y :: Word32. (wordToN x `binLt` wordToN y) = x < y
ltCorrect :: Word32 -> Word32 -> Bool
ltCorrect x y = (wordToN x `binLt` wordToN y) == (x < y)

instance Ord N where
  (<) = binLt
  a <= b = a < b || a == b
  a >= b = not (a < b)

binAdd :: N -> N -> N
binAdd (N as) (N bs) = N (loop False as bs)
  where
    loop _ [] [] = []
    loop carry (a:as) (b:bs) =
      let c = a `xor` b `xor` carry
          carry' = carry `xor` ((a `xor` carry) && (b `xor` carry))
          cs = loop carry' as bs
      in c : cs

-- Correctness: forall x, y :: Word32. nToWord (wordToN x `binAdd` wordToN y) = x + y
addCorrect :: Word32 -> Word32 -> Bool
addCorrect x y = nToWord (wordToN x `binAdd` wordToN y) == x + y

binSub :: N -> N -> N
binSub (N as) (N bs) = N (loop False as bs)
  where
    loop _ [] [] = []
    loop carry (a:as) (b:bs) =
      let c = a `xor` b `xor` carry
          carry' = carry `xor` ((a `xor` b) && (b `xor` carry))
          cs = loop carry' as bs
      in c : cs

-- Correctness: forall x, y :: Word32. nToWord (wordToN x `binSub` wordToN y) = x - y
subCorrect :: Word32 -> Word32 -> Bool
subCorrect x y = nToWord (wordToN x `binSub` wordToN y) == x - y

binMul :: N -> N -> N
binMul (N as) (N bs) = loop as bs
  where
    loop _ [] = 0
    loop as (b:bs) =
      let part = if b then N as else 0
       in part + loop (False : take 31 as) bs

-- Correctness: forall x, y :: Word32. nToWord (wordToN x `binMul` wordToN y) = x * y
mulCorrect :: Word32 -> Word32 -> Bool
mulCorrect x y = nToWord (wordToN x `binMul` wordToN y) == x * y

instance Num N where
  fromInteger = wordToN . fromInteger
  (+) = binAdd
  (-) = binSub
  (*) = binMul
  signum x = if x == 0 then 0 else 1
  abs = id

instance Real N where
  toRational = toRational . nToWord

instance Enum N where
  toEnum = wordToN . toEnum
  fromEnum = fromEnum . nToWord

binQuotRem :: N -> N -> (N, N)
binQuotRem (N ns) d = loop (reverse ns) d [] 0
  where
    loop [] _ q r = (N q, r)
    loop (n:ns) d q r =
      let r' = N (n : take 31 (getN r))
          (q', r'') =
              if r' >= d
                 then (True : q, r' - d)
                 else (False : q, r')
       in loop ns d q' r''

binQuotRemCorrect :: Word32 -> Word32 -> Bool
binQuotRemCorrect x y =
  let (q, r) = binQuotRem (wordToN x) (wordToN y)
      (q', r') = quotRem x y
  in (nToWord q == q') && (nToWord r == r')

instance Integral N where
  toInteger = toInteger . nToWord
  quotRem = binQuotRem
