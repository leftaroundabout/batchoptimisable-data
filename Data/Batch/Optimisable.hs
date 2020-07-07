-- |
-- Module      : Data.Batch.Optimisable
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeInType      #-}
{-# LANGUAGE KindSignatures  #-}


module Data.Batch.Optimisable
   ( SystemCapabilities
   , BatchOptimisable(..)
   ) where

import Data.Kind(Type)
import Data.Traversable
import Data.Foldable as Foldable

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Control.Monad.Trans.State.Strict as SSM

data SystemCapabilities = SystemCapabilities

newtype OptimiseM a = OptimiseM { runOptimiseM :: SystemCapabilities -> IO a }

class BatchOptimisable d where
  data Optimised d (t :: Type->Type) :: Type
  peekOptimised :: Traversable t => Optimised d t -> t d
  optimiseBatch :: (Traversable t, BatchOptimisable d')
                     => (Optimised d t -> Optimised d' t) -> t d -> OptimiseM (t d')

instance BatchOptimisable Int where
  data Optimised Int t
    = IntVector { getIntVector :: VU.Vector Int
                , intVecShape :: t ()
                }
  peekOptimised (IntVector vals shape)
        = (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals VU.! i, i+1)
  optimiseBatch f input = OptimiseM $ \SystemCapabilities -> do
      let n = Foldable.length input
      valV <- VUM.unsafeNew n
      shape <- (`evalStateT`0) . (`traverse`input) $ \x -> do
         i <- get
         VUM.write valV i x
         put $ i+1
         pure ()
      vals <- VU.freeze valV
      pure . peekOptimised . f $ IntVector vals shape
  
