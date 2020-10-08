-- |
-- Module      : Data.Batch.Optimisable.Numerical
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ScopedTypeVariables    #-}


module Data.Batch.Optimisable.Numerical where

import qualified Prelude as Hask
import Data.Traversable
import Control.Category.Constrained.Prelude hiding (Traversable(..), forM)
import Control.Arrow.Constrained

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe
   (unsafeZipTraversablesWith, Optimised(..), VUOptimised(..))

import Data.VectorSpace
import Math.LinearMap.Category
import Math.VectorSpace.ZeroDimensional

import qualified Data.Vector.Unboxed as VU

import Control.Monad ((<=<))
import Control.Monad.Trans.State
import qualified Data.Foldable as Fldb


class (BatchOptimisable n, Num n) => BatchableNum n where
  optimisedZero :: Traversable τ => τ a -> OptimiseM σ (Optimised n σ τ)
  negateOptimised :: Optimised n σ τ
         -> OptimiseM σ (Optimised n σ τ)
  unsafeAddOptimised :: Traversable τ
         => Optimised n σ τ -- ^ Input batches,
         -> Optimised n σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised n σ τ)
  unsafeSubtractOptimised :: Traversable τ
         => Optimised n σ τ -- ^ Input batches,
         -> Optimised n σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised n σ τ)
  unsafeMulOptimised :: Traversable τ
         => Optimised n σ τ -- ^ Input batches,
         -> Optimised n σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised n σ τ)


instance BatchableNum Double where
  optimisedZero shp = allocateBatch $ fmap (const 0) shp
  unsafeAddOptimised (DoubleVectorOptim (VUOptimised shp xs))
                     (DoubleVectorOptim (VUOptimised _ ys))
      = pure . DoubleVectorOptim . VUOptimised shp $ VU.zipWith (+) xs ys
  negateOptimised (DoubleVectorOptim (VUOptimised shp xs))
      = pure . DoubleVectorOptim . VUOptimised shp $ VU.map negate xs
  unsafeSubtractOptimised (DoubleVectorOptim (VUOptimised shp xs))
                     (DoubleVectorOptim (VUOptimised _ ys))
      = pure . DoubleVectorOptim . VUOptimised shp $ VU.zipWith (-) xs ys
  unsafeMulOptimised (DoubleVectorOptim (VUOptimised shp xs))
                     (DoubleVectorOptim (VUOptimised _ ys))
      = pure . DoubleVectorOptim . VUOptimised shp $ VU.zipWith (*) xs ys

