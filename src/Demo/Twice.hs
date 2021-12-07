
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"     @-}

module Demo.Twice where

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect twice @-}
twice :: (a -> a) -> a -> a
twice f x = f (f x)

-- these specs are not compatible with reflection; it's "viral"
-- {-@ inc :: x:Int -> {z:Int|z=x+1} @-}
-- {-@ inc :: x:{v:Int|v>0} -> {z:Int|z=x+1} @-}

{-@ reflect inc @-}
inc :: Int -> Int
inc x = x + 1

{-@ inc2 :: x:Int -> {z:Int|z=x+2} @-}
inc2 :: Int -> Int
inc2 x = inc (inc x)

{-@ test1 :: z:{v:Int|v>0} -> {v:Int|v=z+2} @-}
test1 :: Int -> Int
test1 x = twice inc x

{-@ reflect quad @-}
{-@ quad :: (a -> a) -> a -> a @-}
quad = twice twice

{-@ reflect fourtimes @-}
{-@ fourtimes :: Int -> Int @-}
fourtimes = quad inc

{-@ test2 :: z:Int -> {v:Int|v=z+4} @-}
test2 :: Int -> Int
test2 x = fourtimes x

-- Takes 2 minutes to check

-- {-@ reflect qq @-}
-- {-@ qq :: Int -> Int @-}
-- qq = quad quad inc

-- {-@ test3 :: z:Int -> {v:Int|v=z+256} @-}
-- test3 :: Int -> Int
-- test3 x = qq x

-- making this polymorphic doesn't work because our theorem below requires the
-- output to be of the same type as the first parameter

-- {-@ applyN :: n:Nat -> (a -> a) -> a -> a / [n] @-}
-- applyN :: Int -> (a -> a) -> a -> a

{-@ reflect applyN @-}
{-@ applyN :: n:Nat -> (Nat -> Nat) -> Nat -> Nat / [n] @-}
applyN :: Int -> (Int -> Int) -> Int -> Int
applyN n f x | n <= 0 = x
applyN n f x = f (applyN (n-1) f x)

{-@ manytimes1 :: {v:Nat|v=10} @-}
manytimes1 :: Int
manytimes1 = applyN 10 inc 0

-- can't seem to automatically prove this
-- {-@ manytimes :: z:Nat -> {v:Nat|v=z} @-}
{-@ reflect manytimes @-}
{-@ manytimes :: Nat -> Nat @-}
manytimes :: Int -> Int
manytimes n = applyN n inc 0

-- a separate proof by induction works
{-@ manytimesThm :: n:Nat -> {manytimes n == n} @-}
manytimesThm :: Int -> Proof
manytimesThm 0
  = applyN 0 inc 0 == 0
  === 0 == 0
  *** QED
manytimesThm n | n > 0
  = applyN n inc 0 == n
  === inc (applyN (n-1) inc 0) == n
  === inc (manytimes (n-1)) == n
  ? manytimesThm (n-1)
  === inc (n-1) == n
  === (n-1) + 1 == n
  === n == n
  *** QED

-- many steps can be skipped
{-@ manytimesThm1 :: n:Nat -> {manytimes n == n} @-}
manytimesThm1 :: Int -> Proof
manytimesThm1 0
  = applyN 0 inc 0 == 0
  *** QED
manytimesThm1 n | n > 0
  = applyN n inc 0 == n ? manytimesThm1 (n-1)
  *** QED
