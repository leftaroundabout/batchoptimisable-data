-- |
-- Module      : Data.Batch.Optimisable.LinearMaps
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}


module Data.Batch.Optimisable.LinearMaps where

import qualified Prelude as Hask
import Data.Traversable
import Control.Category.Constrained.Prelude hiding (Traversable(..), forM)

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe
   (unsafeZipTraversablesWith, Optimised(..))

import Data.VectorSpace
import Math.LinearMap.Category
import Math.VectorSpace.ZeroDimensional

import Control.Monad.Trans.State
import qualified Data.Foldable as Fldb


class (BatchOptimisable v, LinearSpace v, Scalar v ~ s)
   => BatchableLinFuns s v where
  sampleLinFunBatch :: ( TensorSpace w, BatchOptimisable w
                       , Scalar w ~ s, Traversable τ )
        => Optimised (LinearFunction s v w) σ τ
           -> OptimiseM σ (τ (LinearMap s v w))
  sampleLinFunLinFunBatch :: ( BatchableLinFuns s u
                             , TensorSpace w, BatchOptimisable w
                             , Scalar w ~ s, Traversable τ )
        => Optimised (LinearFunction s (LinearFunction s v u) w) σ τ
           -> OptimiseM σ (τ (Tensor s v (LinearMap s u w)))

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

instance ∀ s v w
         . ( Num' s, BatchableLinFuns s v, BatchableLinFuns s w )
    => BatchableLinFuns s (LinearFunction s v w) where
  sampleLinFunBatch = fmap (fmap $ \t
              -> LinearMap . LinearFunction
                   $ \fvw -> contractTensorMap . fmap
                              (LinearFunction $ \w
                                 -> fmap (LinearFunction $ \q ->
                                             (applyLinear-+$>q) $ w)
                                    -+$> t)
                              . sampleLinearFunction -+$> fvw )
              . sampleLinFunLinFunBatch

-- tensorizeOptdLinearFunction
--   :: Optimised (LinearFunction s (LinearFunction s (LinearFunction s x y) u) w) σ τ
--        -> Optimised (LinearFunction s w (Tensor s v u)) σ τ
-- tensorizeOptdLinearFunction = undefined

-- linfuncizeTensorLinMap :: LinearMap s w (Tensor s v u)
--            -+> Tensor s (LinearFunction s x y) (LinearMap s u w)
-- linfuncizeTensorLinMap = undefined

instance BatchOptimisable (ZeroDim s) where
  data Optimised (ZeroDim s) σ τ
        = ZeroDimBatch {getPseudoOptZeroDimBatch :: τ (ZeroDim s)}
  allocateBatch = pure . ZeroDimBatch
  peekOptimised = pure . getPseudoOptZeroDimBatch


instance (Num' s, BatchableLinFuns s s)
     => BatchableLinFuns s (ZeroDim s) where
  sampleLinFunBatch (LinFuncOptdBatch shp _) = do
     return $ fmap (const zeroV) shp

instance (BatchableLinFuns s x, BatchableLinFuns s y)
     => BatchableLinFuns s (x,y) where
  sampleLinFunBatch (LinFuncOptdBatch shp xyos) = do
     xZeroes <- allocateBatch $ fmap (const zeroV) shp
     yZeroes <- allocateBatch $ fmap (const zeroV) shp
     xResos <- sampleLinFunBatch . LinFuncOptdBatch shp
                 $ xyos . \oxs -> OptimisedTuple oxs yZeroes
     yResos <- sampleLinFunBatch . LinFuncOptdBatch shp
                 $ xyos . \oys -> OptimisedTuple xZeroes oys
     return $ unsafeZipTraversablesWith
               (\(LinearMap xw) (LinearMap yw) -> LinearMap (Tensor xw, Tensor yw))
               xResos yResos
