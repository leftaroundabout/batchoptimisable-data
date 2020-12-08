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
{-# LANGUAGE RankNTypes, UnicodeSyntax   #-}
{-# LANGUAGE ConstraintKinds              #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained (arr)

import Data.Batch.Optimisable
import Data.Batch.Optimisable.NativeC

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import Data.AdditiveGroup
import Data.VectorSpace
import Data.Basis
import Math.LinearMap.Category
import Math.Category.SymbolicNumFunction hiding ((===))

import GHC.Exts (IsList(..))
import GHC.TypeLits (KnownNat)
import Control.Arrow (first)


type T dims = MultiArray dims Double
type dims++>dims' = T dims +> T dims'

type EqShow t = (Eq t, Show t)


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
     , testProperty "C-double linear maps"
      $ \(l :: ['[4,3]++>'[4,2,5]])
            -> runWithCapabilities cpb (optimiseBatch pure l) === l
     , testProperty "C-double linear functions"
      $ \(l :: ['[3,2]++>'[4,3]])
         -> let l' = (applyLinear-+$>) <$> l
            in (arr<$>runWithCapabilities cpb (optimiseBatch pure $ l')) === l
     , testProperty "Tuples"
      $ \(l :: [((Int, CDoubleArray 3), '[2,3]++>'[4,5])])
            -> runWithCapabilities cpb (optimiseBatch pure l) === l
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
     , testProperty "Commutativity of ^+^"
      $ \(u :: MultiArray '[83] Double) v -> u^+^v ≈≈≈ v^+^u
     , testProperty "Identity linear map"
      $ \(f :: '[3,7]++>'[5])
            -> id . f . id ≈≈≈ f
     , testProperty "Linearity of linear maps"
      $ \(f :: '[5]++>'[7]) v μ w
            -> (f $ v^+^μ*^w) ≈≈≈ (f $ v) ^+^ μ*^(f $ w)
     , testProperty "Linear combination of linear maps"
      $ \f (g :: '[9]++>'[43]) μ v
            -> (f^+^μ*^g $ v) ≈≈≈ (f $ v) ^+^ μ*^(g $ v)
     , testProperty "Composition/multiplication of linear maps"
      $ \(f :: '[4,5]++>'[6]) (g :: '[1,2,3]++>'[4,5]) v
            -> (f . g $ v) ≈≈≈ (f $ g $ v)
     , testProperty "Associativity of composition/multiplication"
      $ \(f :: '[5,6]++>'[7]) (g :: '[2,3,4]++>'[5,6]) (h :: '[9]++>'[2,3,4])
            -> (f . g) . h ≈≈≈ f . (g . h)
     , testProperty "Bilinearity of tensor product"
      $ \u (v :: T '[12]) μ w (x :: T '[13]) ν
            -> (u^+^μ*^v) ⊗ (w^+^ν*^x)
                 ≈≈≈ u⊗w ^+^ μ*^(v⊗w) ^+^ ν*^(u⊗x) ^+^ (μ*ν)*^(v⊗x)
     ]
   , testGroup "Element-wise mapping (optimised)"
     [ testProperty "Identity function"
      $ \(l :: [CDoubleArray 57])
            -> runWithCapabilities cpb (optimiseBatch (numFmapArrayBatchOptimised id)
                                        l ) === l
     , testProperty "Absolute value"
      $ \(l :: [CDoubleArray 57])
            -> runWithCapabilities cpb (optimiseBatch
                   (numFmapArrayBatchOptimised (alg abs))
                                        l )
                       === (mapArray abs <$> l)
     , testProperty "Constant addition"
      $ \(l :: [CDoubleArray 17])
            -> optimisedFmapCorrect cpb (\x -> x+1) l
     , testProperty "Self-addition"
      $ \(l :: [CDoubleArray 9])
            -> optimisedFmapCorrect cpb (\x -> x+x) l
     , testProperty "Polynomial"
      $ \(l :: [CDoubleArray 5])
            -> optimisedFmapCorrect cpb (\x -> x^3 + 4*x - 7) l
     , testProperty "Logarithm"
      $ \(l :: [CDoubleArray 2])
            -> optimisedFmapCorrect cpb (log . (+0.1) . abs) l
     , testProperty "Combination elementary function"
      $ \(l :: [CDoubleArray 2])
            -> optimisedFmapCorrect cpb (\x ->
                 abs (tan $ cos x) ** log (cosh x)
                 - atanh (sin x) * logBase (2 + x*sinh x) (tanh x + 3) ) l
     ]
   ]

optimisedFmapCorrect :: ( KnownNat n )
      => SystemCapabilities -> (∀ n . Floating n => n -> n)
                  -> [CDoubleArray n] -> QC.Property
optimisedFmapCorrect cpb f l = runWithCapabilities cpb (optimiseBatch
                   (numFmapArrayBatchOptimised (alg f)) l )
                       ≈≈≈≈ (mapArray f <$> l)
 where l≈≈≈≈m = QC.conjoin $ zipWith (≈≈≈) l m

infix 4 ≈≈≈
(≈≈≈) :: (Eq v, Show v, InnerSpace v, Scalar v ~ Double)
        => v -> v -> QC.Property
a≈≈≈b
  | magnitude (a^-^b) > max la lb*1e-9  = a===b
  | otherwise                           = a===a
 where la = magnitude a
       lb = magnitude b
       d = a ^-^ b

