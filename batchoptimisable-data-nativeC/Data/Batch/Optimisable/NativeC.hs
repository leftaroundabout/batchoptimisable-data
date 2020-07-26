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
   , MultiArray
   , CIntArray, CLongArray, CFloatArray, CDoubleArray
   ) where

import Data.Batch.Optimisable.NativeC.Internal
import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe

