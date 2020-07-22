-- |
-- Module      : Data.Batch.Optimisable.NativeC
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


module Data.Batch.Optimisable.NativeC (
     module Data.Batch.Optimisable
   -- * Batch-packed data
   , CIntArray
   ) where

import Data.Batch.Optimisable

import Data.Kind(Type)
import Data.Traversable
import Data.Foldable as Foldable

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

import Control.Monad
import Control.Arrow (first)

import qualified Test.QuickCheck as QC

import System.IO.Unsafe

data CIntArray = CIntArray
