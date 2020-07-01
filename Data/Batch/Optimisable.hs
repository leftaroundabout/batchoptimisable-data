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

data SystemCapabilities = SystemCapabilities

newtype OptimiseM a = OptimiseM { runOptimiseM :: IO a }

class BatchOptimisable d where
  type Optimised d (t :: Type->Type) :: Type
  peekOptimised :: Traversable t => Optimised d t -> t d
  optimiseBatch :: (Traversable t, BatchOptimisable) => t d -> Optimised d t

