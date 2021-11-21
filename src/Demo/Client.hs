{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module Demo.Client where

import Language.Haskell.Liquid.Equational

import Demo.Lib
import Demo.Twice
import Demo.Loop
import Demo.Loop1

-- bump :: Int -> Int
-- bump n = if n > 0 then incr n else 0

data Simple = A | B | C

{-@ reflect test @-}
test :: Simple -> Maybe Bool
test A = Just True
test _ = Nothing

{-@ testProof :: {test A == Just True} @-}
testProof :: Proof
testProof =
  test A ==. Just True
  *** QED
