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
   , testProperty "Retrieve single indices"
     $ \(l :: [Int]) i -> runWithCapabilities cpb (do
                            optd <- allocateBatch l
                            peekSingleSample i optd)
                           === if i>=0 && i<length l then Just (l!!i)
                                                     else Nothing
   ]


