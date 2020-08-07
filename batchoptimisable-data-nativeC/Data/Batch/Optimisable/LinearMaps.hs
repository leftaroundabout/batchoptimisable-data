-- |
-- Module      : Data.Batch.Optimisable.LinearMaps
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}


module Data.Batch.Optimisable.LinearMaps where

import Data.Batch.Optimisable

import Data.VectorSpace
import Math.LinearMap.Category

import Control.Monad
import Control.Monad.Trans.State
import qualified Data.Foldable as Fldb


class (BatchOptimisable v, LinearSpace v, Scalar v ~ s)
   => BatchableLinFuns s v where
  sampleLinFunBatch :: ( TensorSpace w, BatchOptimisable w
                       , Scalar w ~ s, Traversable τ )
        => Optimised (LinearFunction s v w) σ τ
           -> OptimiseM σ (τ (LinearMap s v w))

instance ∀ s v w
         . ( BatchableLinFuns s v
           , TensorSpace w, BatchOptimisable w, Scalar w ~ s
           )
    => BatchOptimisable (LinearFunction s v w) where
  data Optimised (LinearFunction s v w) σ τ
    = LinFuncOptdBatch {
             lfbShape :: τ ()
           , runOptdLinFuncBatch
                :: Optimised v σ τ
                  -> OptimiseM σ (Optimised w σ τ) }
  allocateBatch batch = pure . LinFuncOptdBatch (const()<$>batch)
           $ \a -> do
       inputs <- peekOptimised a
       outputs <- (`evalStateT`Fldb.toList batch) . forM inputs $ \x -> do
             (f:fs) <- get
             put fs
             return $ f -+$> x
       allocateBatch outputs
  peekOptimised lfb = fmap (applyLinear-+$>) <$> sampleLinFunBatch lfb
