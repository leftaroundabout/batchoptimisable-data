-- |
-- Module      : Data.Batch.Optimisable.LinearMaps
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE UnicodeSyntax           #-}
{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE ScopedTypeVariables     #-}


module Data.Batch.Optimisable.LinearMaps where

import qualified Prelude as Hask
import Data.Traversable
import Control.Category.Constrained.Prelude hiding (Traversable(..), forM)
import Control.Arrow.Constrained

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe
   (unsafeZipTraversablesWith, Optimised(..), VUOptimised(..))
import Data.Batch.Optimisable.Numerical

import Data.VectorSpace
import Math.LinearMap.Category
import Math.VectorSpace.ZeroDimensional
import Data.VectorSpace.Free

import qualified Data.Vector.Unboxed as VU

import Control.Monad ((<=<))
import Control.Monad.Trans.State
import qualified Data.Foldable as Fldb

import Data.Kind (Type)


class (BatchOptimisable v, LinearSpace v, Scalar v ~ s, BatchableNum s)
   => BatchableLinFuns s v | v->s where
  sampleLinFunBatch :: ( TensorSpace w, BatchOptimisable w
                       , Scalar w ~ s, Traversable τ )
        => Optimised (LinearFunction s v w) σ τ
           -> OptimiseM σ (τ (LinearMap s v w))
  sampleLinFunLinFunBatch :: ( BatchableLinFuns s u
                             , TensorSpace w, BatchOptimisable w
                             , Scalar w ~ s, Traversable τ )
        => Optimised (LinearFunction s (LinearFunction s v u) w) σ τ
           -> OptimiseM σ (τ (Tensor s v (LinearMap s u w)))
  optimisedZeroV :: Traversable τ => τ a -> OptimiseM σ (Optimised v σ τ)
  negateVOptimised :: Optimised v σ τ
         -> OptimiseM σ (Optimised v σ τ)
  unsafeAddVOptimised :: Traversable τ
         => Optimised v σ τ -- ^ Input batches,
         -> Optimised v σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised v σ τ)
  unsafeSubtractVOptimised :: Traversable τ
         => Optimised v σ τ -- ^ Input batches,
         -> Optimised v σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised v σ τ)
  unsafeScaleOptimised :: Traversable τ
         => Optimised s σ τ -- ^ Input batches,
         -> Optimised v σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised v σ τ)

newtype LinFuncOnBatch (s :: Type) σ (τ :: Type->Type) (v :: Type) (w :: Type)
    = LinFuncOnBatch { runLFOnBatch :: Optimised v σ τ
                                    -> OptimiseM σ (Optimised w σ τ) }

instance ∀ s v w
         . ( BatchableLinFuns s v
           , TensorSpace w, BatchOptimisable w, Scalar w ~ s
           )
    => BatchOptimisable (LinearFunction s v w) where
  data Optimised (LinearFunction s v w) σ τ
    = LinFuncOptdBatch {
             lfbShape :: τ ()
           , runOptdLinFuncBatch :: LinFuncOnBatch s σ τ v w }
  allocateBatch batch = pure . LinFuncOptdBatch (const()<$>batch) . LinFuncOnBatch
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

instance BatchableLinFuns Double Double where
  sampleLinFunBatch (LinFuncOptdBatch shp (LinFuncOnBatch f)) = do
     inputs <- allocateBatch $ const 1 <$> shp
     results <- f inputs
     fmap (fmap LinearMap) $ peekOptimised results
  optimisedZeroV = optimisedZero
  unsafeAddVOptimised = unsafeAddOptimised
  negateVOptimised = negateOptimised
  unsafeSubtractVOptimised = unsafeSubtractOptimised
  unsafeScaleOptimised = unsafeMulOptimised

instance (BatchableLinFuns s x, BatchableLinFuns s y)
     => BatchableLinFuns s (x,y) where
  sampleLinFunBatch (LinFuncOptdBatch shp (LinFuncOnBatch xyos)) = do
     xZeroes <- allocateBatch $ fmap (const zeroV) shp
     yZeroes <- allocateBatch $ fmap (const zeroV) shp
     xResos <- sampleLinFunBatch . LinFuncOptdBatch shp . LinFuncOnBatch
                 $ xyos . \oxs -> OptimisedTuple oxs yZeroes
     yResos <- sampleLinFunBatch . LinFuncOptdBatch shp . LinFuncOnBatch
                 $ xyos . \oys -> OptimisedTuple xZeroes oys
     return $ unsafeZipTraversablesWith
               (\(LinearMap xw) (LinearMap yw) -> LinearMap (Tensor xw, Tensor yw))
               xResos yResos



instance Traversable τ => Category (LinFuncOnBatch s σ τ) where
  type Object (LinFuncOnBatch s σ τ) v = (BatchableLinFuns s v)
  id = LinFuncOnBatch pure
  LinFuncOnBatch vws . LinFuncOnBatch uvs
   = LinFuncOnBatch $ \uos -> do
        vos <- uvs uos
        vws vos

instance (Traversable τ, BatchableLinFuns s s, Num' s)
             => Cartesian (LinFuncOnBatch s σ τ) where
  type UnitObject (LinFuncOnBatch s σ τ) = ZeroDim s
  swap = LinFuncOnBatch $ \(OptimisedTuple xs ys)
               -> return $ OptimisedTuple ys xs
  attachUnit = LinFuncOnBatch $ \xs -> do
      units <- allocateBatch . fmap (const Origin) =<< peekBatchShape xs
      return $ OptimisedTuple xs units
  detachUnit = LinFuncOnBatch $ \(OptimisedTuple xs _) -> pure xs
  regroup = LinFuncOnBatch $ \(OptimisedTuple xs (OptimisedTuple ys zs))
               -> return $ OptimisedTuple (OptimisedTuple xs ys) zs
  regroup' = LinFuncOnBatch $ \(OptimisedTuple (OptimisedTuple xs ys) zs)
               -> return $ OptimisedTuple xs (OptimisedTuple ys zs)

instance (Traversable τ, BatchableLinFuns s s, Num' s)
             => Morphism (LinFuncOnBatch s σ τ) where
  LinFuncOnBatch f *** LinFuncOnBatch g
     = LinFuncOnBatch $ \(OptimisedTuple xs ys) -> do
           fxs <- f xs
           gys <- g ys
           return $ OptimisedTuple fxs gys

instance (Traversable τ, BatchableLinFuns s s, Num' s)
             => PreArrow (LinFuncOnBatch s σ τ) where
  LinFuncOnBatch f &&& LinFuncOnBatch g
     = LinFuncOnBatch $ \xs -> do
           fxs <- f xs
           gxs <- g xs
           return $ OptimisedTuple fxs gxs
  terminal = LinFuncOnBatch $ \xs -> do
      shp <- peekBatchShape xs
      return . ZeroDimBatch $ fmap (const Origin) shp
  fst = LinFuncOnBatch $ \(OptimisedTuple xs _) -> pure xs
  snd = LinFuncOnBatch $ \(OptimisedTuple _ ys) -> pure ys

instance (BatchOptimisable v, BatchableLinFuns s f, Traversable τ)
              => AdditiveGroup (LinFuncOnBatch s σ τ v f) where
  zeroV = LinFuncOnBatch $ \xs -> do
    shp <- peekBatchShape xs
    optimisedZeroV shp
  LinFuncOnBatch f ^+^ LinFuncOnBatch g
         = LinFuncOnBatch $ \xs -> do
    fxs <- f xs
    gxs <- g xs
    unsafeAddVOptimised fxs gxs
  negateV (LinFuncOnBatch f) = LinFuncOnBatch $ negateVOptimised <=< f

class ( BatchableLinFuns (Scalar v) v, FreeVectorSpace v
      , Category (PointwiseMapCategory v), Object (PointwiseMapCategory v) (Scalar v) )
         => BatchableFreeSpace v where
  type PointwiseMapCategory v :: Type -> Type -> Type
  unsafeMulPointwiseOptimised :: Traversable τ
         => Optimised v σ τ -- ^ Input batches,
         -> Optimised v σ τ -- ^ must have same shape
         -> OptimiseM σ (Optimised v σ τ)
  fmapFreeVecOptimised :: PointwiseMapCategory v (Scalar v) (Scalar v)
                    -> Optimised v σ τ -> OptimiseM σ (Optimised v σ τ)


instance BatchableFreeSpace Double where
  type PointwiseMapCategory Double = (->)
  unsafeMulPointwiseOptimised = unsafeMulOptimised
  fmapFreeVecOptimised f (DoubleVectorOptim (VUOptimised shp xs))
      = pure . DoubleVectorOptim . VUOptimised shp $ VU.map f xs
