-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

import Data.Batch.Optimisable
import Data.Batch.Optimisable.NativeC

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

main :: IO ()
main = do
  cpb <- detectCpuCapabilities
  defaultMain $ testGroup "Tests"
   [ testProperty "Retrieve C-integer arrays"
     $ \(l :: [CIntArray 8]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   , testProperty "Retrieve C-long arrays"
     $ \(l :: [CLongArray 37]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   , testProperty "Retrieve C-float arrays"
     $ \(l :: [CFloatArray 9]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   , testProperty "Retrieve C-double arrays"
     $ \(l :: [CDoubleArray 13]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   ]


