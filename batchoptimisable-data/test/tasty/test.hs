-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables #-}

import Data.Batch.Optimisable

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

main :: IO ()
main = do
  cpb <- detectCpuCapabilities
  defaultMain $ testGroup "Tests"
   [ testProperty "Retrieve optimised integer list"
     $ \(l :: [Int]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   , testProperty "Retrieve optimised tuple list"
     $ \(l :: [(Int,Int)]) -> runWithCapabilities cpb (optimiseBatch pure l) === l
   ]


