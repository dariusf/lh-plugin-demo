
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"     @-}

module Demo.Twice where

{-@ reflect twice @-}
twice :: (a -> a) -> a -> a
twice f x = f (f x)

{-@ reflect inc @-}
inc :: Int -> Int
inc x = x + 1

{-@ test1 :: z:Int -> {v:Int|v=z+2} @-}
test1 :: Int -> Int
test1 x = twice inc x
