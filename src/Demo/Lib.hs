
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination"     @-}
{-@ LIQUID "--ple"     @-}

{- LIQUID "--higherorder"     @-}

module Demo.Lib where

import Prelude hiding (replicate, map)
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ prop1 :: f:(a -> a) -> g:(a -> a) -> x:a
          -> {v: Proof | f (g x) == compose f g x } @-}
prop1 :: (a -> a) -> (a -> a) -> a -> Proof
prop1 f g x = trivial


{-@ prop2 :: f:(a -> a) -> g:(a -> a) -> x:a
          -> {v: Proof | compose f g x == compose f g x } @-}
prop2 :: (a -> a) -> (a -> a) -> a -> Proof
prop2 f g x = trivial

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ incr :: Pos -> Pos @-}
incr :: Int -> Int
incr x = x + 1

-- {-@ reflect compose @-}
-- compose :: (b -> c) -> (a -> b) -> a -> c
-- compose f g x = f (g x)

{- axiomatize twice @-}
{-@ reflect twice @-}
twice :: (a -> a) -> a -> a
twice f x = f (f x)

{- inc :: { x : Int | x > 0 } -> { x : Int | x > 1 } @-}
{- inc :: z:{ x : Int | x > 0 } -> {v:Int|v=z+1} @-}

{-@ inc :: z:Int -> {v:Int|v=z+1} @-}
inc :: Int -> Int
inc x = x + 1

{- test1 :: z:{ y : Int | y > 0 } -> { v :  Int | v = z + 2 } @-}
{- test1 :: z:Int -> {v:Int|v=twice incr x} @-}
{-@ test1 :: z:Int -> {v:Int|v=z+2} @-}
test1 :: Int -> Int
test1 x = inc (inc x)
-- test1 x = twice inc x

{-@ reflect fib @-}
{-@ fib :: i:Int -> Int  @-}
fib :: Int -> Int
fib i | i <= 0    = 0 -- == doesn't work
      | i == 1    = 1
      | otherwise = fib (i-1) + fib (i-2)

{-@ fibCongr :: i:Nat -> j:Nat -> {i == j => fib i == fib j} @-}
fibCongr :: Int -> Int -> Proof
fibCongr _ _ = trivial

-- this is not supposed to work?
{-@ fibOne :: () ->  { fib 1 == 1 } @-}
fibOne () = trivial

{-

calling fib reveals impl at logical level

fib :: i:Nat
    -> {v:Nat |  v == fib i
              && v == if i == 0 then 0 else
                      if i == 1 then 1 else
                      fib (i-1) + fib (i-2)
       }

-}

{-@ fibEq :: () -> { fib 1 == 1 } @-}
fibEq () = let f1 = fib 1 -- f1:: {f1 == fib 1 && f1 == 1}
          in [f1] *** QED

{-@ fibTwo :: _ -> { fib 2 == 1 } @-}
fibTwo _
  =   fib 2
  === fib 1 + fib 0
  *** QED

{-@ fibThree :: _ -> { fib 3 == 2 } @-}
fibThree _
  =   fib 3
  === fib 2 + fib 1
  === 1     + 1      ? fibTwo () -- "because" operator
  === 2
  *** QED

-- deprecated
-- {-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
-- fibUp i
--   | i == 0
--   =   fib 0 =<= fib 1
--   *** QED
--   | i == 1
--   =   fib 1 =<= fib 1 + fib 0 =<= fib 2
--   *** QED
--   | otherwise
--   =   fib i
--   === fib (i-1) + fib (i-2)
--   =<= fib i     + fib (i-2) ? fibUp (i-1)
--   =<= fib i     + fib (i-1) ? fibUp (i-2)
--   =<= fib (i+1)
--   *** QED

-- https://github.com/ucsd-progsys/liquidhaskell/blob/e2af8fec20e1108b993b7116ec75b4007930aca6/benchmarks/popl18/ple/pos/Fibonacci.hs

{-@ fib1 :: () -> {fib 16 == 987 } @-}
fib1 :: () -> Proof
fib1 () = trivial

fibUp :: Int -> Proof
{-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
fibUp i
  | i == 0
  =   [fib 0, fib 1] *** QED
  | i == 1
  =  [fib 1, fib 0, fib 2] *** QED
  | otherwise
  = [[fib (i+1), fib i] *** QED , fibUp (i-1), fibUp (i-2)] *** QED

{-@ replicate :: Int -> b:Int -> [Int] / [b] @-}
replicate :: Int -> Int -> [Int]
replicate _ n | n <= 0 = []
replicate x n = x : replicate x (n - 1)

-- {-@ map :: (a -> b) -> xs:[a] -> [b] / [len xs] @-}
-- map _ []     = []
-- map f (x:xs) = f x : map f xs

{-@ propOnePlusOne :: () ->  {v: Proof | 1 + 1 == 2} @-}
propOnePlusOne () = trivial

{-@ reflect id @-}
id :: a -> a
id x = x

-- {-@ reflect compose @-}
-- compose :: (b -> c) -> (a -> b) -> a -> c
-- compose f g x = f (g x)

{-@
(.) :: forall < p :: b -> c -> Bool
              , q :: a -> b -> Bool
              , r :: a -> c -> Bool
              >.
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       f:(y:b -> c<p y>)
    -> g:(z:a -> b<q z>)
    -> x:a -> c<r x>
@-}
(.) f g x = f (g x)

{-@ map :: (a -> b) -> xs:[a] -> [b] @-}
map _ []         = []
map f (x : xs)  = f x : map f xs

-- data Weather = W { temp :: Int, rain :: Int }

-- data Year a = Year [a]
-- {-@ data Year a = Year (ListN a 12) @-}

-- tempAverage :: Year Weather -> Int
-- tempAverage (Year ms) = average months
--   where
--     months            = map temp ms

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

-- {-@ loop :: lo:Nat -> hi:{Nat|lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a @-}
-- loop :: Int -> Int -> a -> (Int -> a -> a) -> a
-- loop lo hi base f = go lo base
--   where
--     go i acc
--       | i < hi    = go (i+1) (f i acc)
--       | otherwise = acc


-- listSum xs  = loop 0 n 0 body
--   where
--     body    = \i acc -> acc + (xs !! i)
--     n       = length xs
