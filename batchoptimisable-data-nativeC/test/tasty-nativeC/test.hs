-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

import Data.Batch.Optimisable
import Data.Batch.Optimisable.NativeC

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import Data.AdditiveGroup
import Data.VectorSpace


main :: IO ()
main = do
  cpb <- detectCpuCapabilities
  defaultMain $ testGroup "Tests"
   [ testGroup "Simple retrieval of optimised"
     [ testProperty "C-integer arrays"
      $ \(l :: [CIntArray 8]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
     , testProperty "C-long arrays"
      $ \(l :: [CLongArray 37]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
     , testProperty "C-float arrays"
      $ \(l :: [CFloatArray 9]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
     , testProperty "C-double arrays"
      $ \(l :: [CDoubleArray 13]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
     ]
   , testGroup "Vector space laws (unoptimised)"
     [ testProperty "Left zero"
      $ \(v :: MultiArray '[4,9] Int) -> zeroV^+^v === v
     , testProperty "Right zero"
      $ \(v :: MultiArray '[7,43,2] Int) -> v^+^zeroV === v
     , testProperty "Associativity"
      $ \(u :: MultiArray '[83] Int) v w -> u^+^(v^+^w) === (u^+^v)^+^w
     ]
   ]


