-- |
-- Module      : Data.Batch.Optimisable.Unsafe
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE UnicodeSyntax       #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DeriveFunctor       #-}


module Data.Batch.Optimisable.Unsafe (
   -- * Batch-packed data
     BatchOptimisable(..)
   , OptimiseM, runWithCapabilities
   -- * System resource bookkeeping
   , SystemCapabilities
   , detectCpuCapabilities
   ) where

import Data.Kind(Type)
import Data.Traversable
import Data.Foldable as Foldable

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

import Control.Monad
import Control.Monad.Trans.State.Strict as SSM
import Control.Arrow (first)

import qualified Test.QuickCheck as QC

import System.IO.Unsafe

data SystemCapabilities = SystemCapabilities

detectCpuCapabilities :: IO SystemCapabilities
detectCpuCapabilities = pure SystemCapabilities

newtype RscReleaseHook = RscReleaseHook { runReleaseHook :: IO () }

type DList a = [a]->[a]

type UniqueStateTag = Type

newtype OptimiseM (s :: UniqueStateTag) a = OptimiseM {
      runOptimiseM :: SystemCapabilities -> IO (a, DList RscReleaseHook) }
  deriving (Functor)

instance Applicative (OptimiseM s) where
  pure x = OptimiseM . const $ pure (x, id)
  OptimiseM fs <*> OptimiseM xs
      = OptimiseM $ \cpbs -> do
          (f, fRscR) <- fs cpbs
          (x, xRscR) <- xs cpbs
          return (f x, fRscR . xRscR)
instance Monad (OptimiseM s) where
  return = pure
  OptimiseM xs >>= f = OptimiseM $ \cpbs -> do
     (x, xRscR) <- xs cpbs
     let OptimiseM ys = f x
     (y, yRscR) <- ys cpbs
     return (y, xRscR . yRscR)

runWithCapabilities :: SystemCapabilities -> (∀ s . OptimiseM s a) -> a
runWithCapabilities cpbs (OptimiseM r) = unsafePerformIO $ do
    (res, rscRs) <- r cpbs
    forM_ (rscRs[]) runReleaseHook
    return res

class BatchOptimisable d where
  data Optimised d (s :: UniqueStateTag) (t :: Type->Type) :: Type
  allocateBatch :: Traversable t => t d -> OptimiseM s (Optimised d s t)
  peekOptimised :: Traversable t => Optimised d s t -> OptimiseM s (t d)
  optimiseBatch :: (Traversable t, BatchOptimisable d')
     => (Optimised d s t -> OptimiseM s (Optimised d' s t))
                -> t d -> OptimiseM s (t d')
  optimiseBatch f xs = OptimiseM $ \sysCaps -> do
      (xVals, xRscR) <- runOptimiseM (allocateBatch xs) sysCaps
      (yVals, yRscR) <- runOptimiseM (f xVals) sysCaps
      (peekd, _) <- runOptimiseM (peekOptimised yVals) sysCaps
      return (peekd, xRscR.yRscR)

instance BatchOptimisable Int where
  data Optimised Int s t
    = IntVector { getIntVector :: VU.Vector Int
                , intVecShape :: t ()
                }
  peekOptimised (IntVector vals shape)
        = pure . (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals `VU.unsafeIndex` i, i+1)
  allocateBatch input = OptimiseM $ \_ -> do
      let n = Foldable.length input
      valV <- VUM.unsafeNew n
      shape <- (`evalStateT`0) . (`traverse`input) $ \x -> do
         i <- get
         VUM.unsafeWrite valV i x
         put $ i+1
         pure ()
      vals <- VU.unsafeFreeze valV
      return (IntVector vals shape, id)

instance (Foldable t, QC.Arbitrary (t ()))
             => QC.Arbitrary (Optimised Int s t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Foldable.length shape
     values <- replicateM n QC.arbitrary
     return $ IntVector (VU.fromList values) shape
  shrink = undefined

newtype x//>//y = BatchedFunction
   { getBatchedFunction :: ∀ t s . Traversable t
       => Optimised x s t -> OptimiseM s (Optimised y s t) }
