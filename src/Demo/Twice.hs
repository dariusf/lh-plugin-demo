
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
