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

import Data.Batch.Optimisable.Unsafe


instance (BatchOptimisable a, BatchOptimisable b) => BatchOptimisable (a,b) where
  data Optimised (a,b) σ τ = OptimisedTuple
         { optimL :: Optimised a σ τ
         , optimR :: Optimised b σ τ }
  allocateBatch xys = do
    xos <- allocateBatch $ fst<$>xys
    yos <- allocateBatch $ snd<$>xys
    return $ OptimisedTuple xos yos
