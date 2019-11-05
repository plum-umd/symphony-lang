{-# language OverloadedStrings #-}
module Example where

import PCL
import Netlist

z :: Int -> Type
z n = foldr Prod Unit (replicate n Boolean)

decomposeZ :: Int -> Term -> [Term]
decomposeZ n = map Fst . go n
  where
    go n t = if n <= 0 then []
                       else t : map Snd (go (n-1) t)

add :: Int -> Term
add n =
  Lam ("args", Prod (z n) (z n)) $
    let xs = decomposeZ n (Fst "args")
        ys = decomposeZ n (Snd "args")
     in addFull F xs ys
  where
    addFull :: Term -> [Term] -> [Term] -> Term
    addFull carry (x:xs) (y:ys) =
      Let "x" x $
      Let "y" y $
      Let "carry" carry $
      Let "t" (("x" `tXor` "carry") `tAnd` ("y" `tXor` "carry")) $
       Pair ("x" `tXor` "y" `tXor` "carry")
            (addFull ("carry" `tXor` "t") xs ys)
    addFull _ _ _ = One

sub :: Int -> Term
sub n =
  Lam ("args", Prod (z n) (z n)) $
    let xs = decomposeZ n (Fst "args")
        ys = decomposeZ n (Snd "args")
     in subFull F xs ys
  where
    subFull :: Term -> [Term] -> [Term] -> Term
    subFull carry (x:xs) (y:ys) =
      Let "x" x $
      Let "y" y $
      Let "carry" carry $
      Let "t" (("x" `tXor` "y") `tAnd` ("y" `tXor` "carry")) $
       Pair ("x" `tXor` "y" `tXor` "carry")
            (subFull ("carry" `tXor` "t") xs ys)
    subFull _ _ _ = One

lt :: Int -> Term
lt n =
  Lam ("args", Prod (z n) (z n)) $
    let xs = reverse $ decomposeZ n (Fst "args")
        ys = reverse $ decomposeZ n (Snd "args")
     in
     go xs ys
  where
    go (x:xs) (y:ys) =
      Let "x" x $
      Let "y" y $
       (tNot "x" `tAnd` "y") `tOr`
        (eqlBit "x" "y" `tAnd` go xs ys)
    go [] [] = F

gcd :: Int -> Int -> Term
gcd n depth =
  Lam ("args", Prod (z n) (z n)) $
    App
    (Fix depth ("f", Prod (z n) (z n) `Arrow` z n)
      (Lam ("args", Prod (z n) (z n)) $
        Let "a" (Fst "args") $
        Let "b" (Snd "args") $
        If (App (eql n) (Pair "b" zero))
        "a"
        (App "f" (Pair "b" (App (Example.rem n depth) (Pair "a" "b")))))) "args"
  where
    zero = foldr Pair One (replicate n F)

eql :: Int -> Term
eql n =
  Lam ("args", Prod (z n) (z n)) $
    let xs = decomposeZ n (Fst "args")
        ys = decomposeZ n (Snd "args")
     in foldr1 tAnd (zipWith eqlBit xs ys)

rem :: Int -> Int -> Term
rem n depth =
  Lam ("args", Prod (z n) (z n)) $
    App
    (Fix depth ("f", Prod (z n) (z n) `Arrow` z n) $
      Lam ("args", Prod (z n) (z n)) $
        Let "n" (Fst "args") $
        Let "d" (Snd "args") $
          If (App (lt n) (Pair "n" "d"))
             "n"
             (App "f" (Pair (App (sub n) (Pair "n" "d")) "d"))
    ) "args"


eqlBit :: Term -> Term -> Term
eqlBit t0 t1 = tNot (tXor t0 t1)

tXor :: Term -> Term -> Term
tXor t0 t1 = App Xor (Pair t0 t1)

tAnd :: Term -> Term -> Term
tAnd t0 t1 = App And (Pair t0 t1)

tOr :: Term -> Term -> Term
tOr t0 t1 = tNot (App And (Pair (tNot t0) (tNot t1)))

tNot :: Term -> Term
tNot t = App Xor (Pair t T)

intToZ :: Int -> Int -> [Bool]
intToZ i = reverse . go i
  where
    go i x =
      if i <= 0
         then []
         else
           let (n, rem) = divMod x (floor (2 ^^ (i-1)))
            in if n > 0
                  then True : go (i-1) rem
                  else False : go (i-1) rem

zToInt :: [Bool] -> Int
zToInt bs = sum (zipWith (*) bsZ bases)
  where
    bsZ = map (\b -> if b then 1 else 0) bs
    bases = 1 : map (2*) bases

testAdd n i j =
  let Just nl = compile (add n)
   in run nl (i ++ j)

-- Check that the bitwise adder matches modular addition on all inputs.
exhaustAdd :: Int -> Bool
exhaustAdd n =
  let top = floor (2 ^^ n) in
  and $ do
  i <- [0..top-1]
  j <- [0..top-1]
  pure (zToInt (testAdd n (intToZ n i) (intToZ n j)) == ((i + j) `mod` top))

testSub n i j =
  let Just nl = compile (sub n)
   in run nl (i ++ j)

-- Check that the bitwise adder matches modular addition on all inputs.
exhaustSub :: Int -> Bool
exhaustSub n =
  let top = floor (2 ^^ n) in
  and $ do
  i <- [0..top-1]
  j <- [0..top-1]
  pure (zToInt (testSub n (intToZ n i) (intToZ n j)) == ((i - j) `mod` top))

testLt n i j =
  let Just nl = compile (lt n)
   in run nl (intToZ n i ++ intToZ n j)

exhaustLt :: Int -> Bool
exhaustLt n =
  let top = floor (2 ^^ n) in
  and $ do
    i <- [0..top-1]
    j <- [0..top-1]
    pure (head (testLt n i j) == (i < j))

testRem n d i j =
  let Just nl = compile (Example.rem n d)
   in zToInt $ run nl (intToZ n i ++ intToZ n j)

testGcd n d i j =
  let Just nl = compile (Example.gcd n d)
   in zToInt $ run nl (intToZ n i ++ intToZ n j)
