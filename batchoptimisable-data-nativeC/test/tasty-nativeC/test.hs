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
{-# LANGUAGE TypeFamilies, TypeOperators  #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude

import Data.Batch.Optimisable
import Data.Batch.Optimisable.NativeC

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import Data.AdditiveGroup
import Data.VectorSpace
import Data.Basis
import Math.LinearMap.Category

import GHC.Exts (IsList(..))
import Control.Arrow (first)


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
   , testGroup "Array indices"
     [ testProperty "List view of basis"
      $ \(i :: Basis (MultiArray '[34,43,54,45] Double))
             -> i === first (fromList . toList) i
     ]
   , testGroup "Vector space laws (unoptimised)"
     [ testProperty "Left zero"
      $ \(v :: MultiArray '[4,9] Int) -> zeroV^+^v === v
     , testProperty "Right zero"
      $ \(v :: MultiArray '[7,43,2] Double) -> v^+^zeroV ≈≈≈ v
     , testProperty "Associativity of ^+^"
      $ \(u :: MultiArray '[83] Int) v w -> u^+^(v^+^w) === (u^+^v)^+^w
     , testProperty "Linearity of linear maps"
      $ \(f :: MultiArray '[5] Double +> MultiArray '[7] Double) v μ w
            -> (f $ v^+^μ*^w) ≈≈≈ (f $ v) ^+^ μ*^(f $ w)
     ]
   ]

infix 4 ≈≈≈
(≈≈≈) :: (Eq v, Show v, InnerSpace v, Scalar v ~ Double)
        => v -> v -> QC.Property
a≈≈≈b
  | magnitude (a^-^b) > max la lb*1e-9  = a===b
  | otherwise                           = a===a
 where la = magnitude a
       lb = magnitude b
       d = a ^-^ b

