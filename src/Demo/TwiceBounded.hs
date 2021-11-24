
module Demo.TwiceBounded where

{-@ type Pos = {v:Int | 0 <= v} @-}
{-@ incz :: Pos -> Pos @-}
incz :: Int -> Int
incz x = x + 1


--    twice.pre(f,x) -> f.pre(x)
-- /\ twice.pre(f,x) /\ f.post(x,y) -> f.pre(y)
-- /\ twice.pre(f,x) /\ f.post(x,y) /\ f.post(y,r) -> twice.post(f,x,res)

{-@
twice :: forall < fpost :: a -> a -> Bool
              , fpre :: a -> Bool
              , twicepre :: a -> Bool
              , twicepost :: a -> a -> Bool
              >.
       {x::a<fpre>, w::a<fpost x> |- a<fpost w> <: a<twicepost x>}
       {x::a<twicepre> |- a<fpost x> <: a<fpre>}
       {x::a<twicepre> |- a<twicepre> <: a<fpre>}
       f:(z:a<fpre> -> a<fpost z>)
    -> x:a<twicepre> -> a<twicepost x>
@-}
twice f x = f (f x)

{-@ incr :: x:Nat -> {v:Nat | v == x + 1} @-}
incr :: Int -> Int
incr x = x + 1

{-@ incr2 :: x:Nat -> {v:Nat | v == x + 2} @-}
incr2 x = twice incr x

{-@ incrrr :: x:{v:Nat| v < 100 } -> {v:Nat | v == x + 1 } @-}
incrrr :: Int -> Int
incrrr x = x + 1

{-@ incrrr2 :: x:{v:Nat| v < 99 } -> {v:Nat | v == x + 2 } @-}
incrrr2 x = twice incrrr x

-- Takes 25 mins to run

{- quad :: forall < fpost :: a -> a -> Bool
              , fpre :: a -> Bool
              , quadpre :: a -> Bool
              , quadpost :: a -> a -> Bool
              >.
        {x::a<quadpre>, y::a<fpost x> |- a<fpost x> <: a<fpre>}
        {x::a<quadpre>, y::a<fpost x>, y2::a<fpost y> |- a<fpost y> <: a<fpre>}
        {x::a<quadpre>, y::a<fpost x>, y2::a<fpost y>, y3::a<fpost y2> |- a<fpost y2> <: a<fpre>}
        {x::a<fpre>, y::a<fpost x>, y2::a<fpost y>, y3::a<fpost y2> |- a<fpost y3> <: a<quadpost x>}
        {x::a<quadpre> |- a<quadpre> <: a<fpre>}
       f:(z:a<fpre> -> a<fpost z>)
    -> x:a<quadpre> -> a<quadpost x>
@-}
-- quad f x = let g = twice twice f in g x

-- {-@ test3 :: x:{v:Nat| v < 97 } -> {v:Nat | v == x + 4 } @-}
-- test3 x = quad incrrr x

-- {-@ test4 :: x:{v:Nat| v < 93 } -> {v:Nat | v == x + 8 } @-}
-- test4 x = quad incrrr2 x

-- {-@ test5 :: x:{v:Nat| v < 94 } -> {v:Nat | v == x + 8 } @-}
-- test5 x = quad incrrr2 x

-- {-@ test6:: x:{v:Nat| v < 93 } -> {v:Nat | v == x + 7 } @-}
-- test6 x = quad incrrr2 x
