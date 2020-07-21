-- |
-- Module      : Data.Batch.Optimisable
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


module Data.Batch.Optimisable (
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

newtype OptimiseM a = OptimiseM {
      runOptimiseM :: SystemCapabilities -> IO (a, DList RscReleaseHook) }
  deriving (Functor)

instance Applicative OptimiseM where
  pure x = OptimiseM . const $ pure (x, id)
  OptimiseM fs <*> OptimiseM xs
      = OptimiseM $ \cpbs -> do
          (f, fRscR) <- fs cpbs
          (x, xRscR) <- xs cpbs
          return (f x, fRscR . xRscR)
instance Monad OptimiseM where
  return = pure
  OptimiseM xs >>= f = OptimiseM $ \cpbs -> do
     (x, xRscR) <- xs cpbs
     let OptimiseM ys = f x
     (y, yRscR) <- ys cpbs
     return (y, xRscR . yRscR)

runWithCapabilities :: SystemCapabilities -> OptimiseM a -> a
runWithCapabilities cpbs (OptimiseM r) = unsafePerformIO $ do
    (res, rscRs) <- r cpbs
    forM_ (rscRs[]) runReleaseHook
    return res

class BatchOptimisable d where
  data Optimised d (t :: Type->Type) :: Type
  peekOptimised :: Traversable t => Optimised d t -> t d
  optimiseBatch :: (Traversable t, BatchOptimisable d')
     => (Optimised d t -> OptimiseM (Optimised d' t)) -> t d -> OptimiseM (t d')

instance BatchOptimisable Int where
  data Optimised Int t
    = IntVector { getIntVector :: VU.Vector Int
                , intVecShape :: t ()
                }
  peekOptimised (IntVector vals shape)
        = (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals VU.!{-unsafeIndex-} i, i+1)
  optimiseBatch f input = OptimiseM $ \sysCaps -> do
      let n = Foldable.length input
      valV <- VUM.unsafeNew n
      shape <- (`evalStateT`0) . (`traverse`input) $ \x -> do
         i <- get
         VUM.write{-unsafeWrite-} valV i x
         put $ i+1
         pure ()
      vals <- VU.freeze{-unsafeFreeze-} valV
      let OptimiseM process = f (IntVector vals shape)
      first peekOptimised <$> process sysCaps

instance (Foldable t, QC.Arbitrary (t ()))
             => QC.Arbitrary (Optimised Int t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Foldable.length shape
     values <- replicateM n QC.arbitrary
     return $ IntVector (VU.fromList values) shape
  shrink = undefined

newtype x//>//y = BatchedFunction
   { getBatchedFunction :: ∀ t . Traversable t
       => Optimised x t -> OptimiseM (Optimised y t) }
