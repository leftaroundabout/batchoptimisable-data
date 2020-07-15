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

import qualified Test.QuickCheck as QC

import System.IO.Unsafe

data SystemCapabilities = SystemCapabilities

detectCpuCapabilities :: IO SystemCapabilities
detectCpuCapabilities = pure SystemCapabilities

newtype OptimiseM a = OptimiseM { runOptimiseM :: SystemCapabilities -> IO a }
  deriving (Functor)

instance Applicative OptimiseM where
  pure = OptimiseM . const . pure
  OptimiseM fs <*> OptimiseM xs = OptimiseM $ \cpbs -> fs cpbs <*> xs cpbs
instance Monad OptimiseM where
  return = pure
  OptimiseM xs >>= f = OptimiseM $ \cpbs -> do
     x <- xs cpbs
     let OptimiseM ys = f x
     ys cpbs

runWithCapabilities :: SystemCapabilities -> OptimiseM a -> a
runWithCapabilities cpbs (OptimiseM r) = unsafePerformIO $ r cpbs

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
      peekOptimised <$> process sysCaps
  
instance (Foldable t, QC.Arbitrary (t ()))
             => QC.Arbitrary (Optimised Int t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Foldable.length shape
     values <- replicateM n QC.arbitrary
     return $ IntVector (VU.fromList values) shape
  shrink = undefined
