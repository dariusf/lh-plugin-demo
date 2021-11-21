
{-@ LIQUID "--no-termination"     @-}

module Demo.Loop1 where

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ loop :: lo:Nat -> hi:{Nat|lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where
    go i acc
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
