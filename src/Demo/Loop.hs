{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination"     @-}
{-@ LIQUID "--ple"     @-}

module Demo.Loop where

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ loop_go :: lo:Nat -> hi:{Nat|lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> i:{Nat|lo <= i} -> a -> a @-}
loop_go :: Int -> Int -> a -> (Int -> a -> a) -> Int -> a -> a
loop_go lo hi base f i acc
  | i < hi = loop_go lo hi base f (i + 1) (f i acc)
  | otherwise = acc

{-@ loop :: lo:Nat -> hi:{Nat|lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = loop_go lo hi base f lo base
  -- where
  --   go i acc
  --     | i < hi    = go (i+1) (f i acc)
  --     | otherwise = acc

    -- The inferred type
    --   VV : {v : GHC.Types.Int | v == i}
    -- .
    -- is not a subtype of the required type
    --   VV : {VV : GHC.Types.Int | lo <= VV}
    -- .
