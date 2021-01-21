-- |
-- Module      : Data.Batch.Optimisable.NativeC
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

module Data.Batch.Optimisable.NativeC (
     module Data.Batch.Optimisable
   -- * Batch-packed data
   , MultiArray, mapArray
   , CIntArray, CLongArray, CFloatArray, CDoubleArray
   , numFmapBatchOptimised
   , numFmapArrayBatchOptimised
   ) where

import Data.Batch.Optimisable.NativeC.Internal
import Data.Batch.Optimisable.NativeC.Instances ()
import Data.Batch.Optimisable.NativeC.Instances.SymbNumFmapping ()
import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe

