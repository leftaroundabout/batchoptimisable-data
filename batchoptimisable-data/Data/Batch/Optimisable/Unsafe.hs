-- |
-- Module      : Data.Batch.Optimisable.Unsafe
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE UnicodeSyntax       #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE DeriveFunctor       #-}


module Data.Batch.Optimisable.Unsafe (
   -- * Batch-packed data
     BatchOptimisable(..)
   , OptimiseM(..), Optimised(..), runWithCapabilities, unsafeIO
   -- ** Batch containers
   , Traversable(..), itraverse
   -- * System resource bookkeeping
   , SystemCapabilities
   , primitiveCapabilities
   , detectCpuCapabilities
   , RscReleaseHook(..)
   -- * Utility
   , unsafeZipTraversablesWith
   , VUOptimised(..)
   ) where

import Data.Kind(Type)
import Data.Traversable
import Control.Lens.Indexed (TraversableWithIndex(..))
import Data.Foldable as Fldb
import Data.Semigroup ((<>))

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.Vector.Unboxed.Mutable as VUM

import Control.Monad
import Control.Monad.Fail
import Control.Monad.Trans.Identity
import Control.Monad.Trans.State.Strict as SSM
import Control.Arrow (first)

import Data.DList (DList)

import qualified Test.QuickCheck as QC

import Data.IORef
import System.IO.Unsafe
import Control.Exception (bracketOnError)

data SystemCapabilities = SystemCapabilities

-- | Bare-bones capabilities that any computer can be expected to
--   have. Mostly intended for debugging.
primitiveCapabilities :: SystemCapabilities
primitiveCapabilities = SystemCapabilities

detectCpuCapabilities :: IO SystemCapabilities
detectCpuCapabilities = pure SystemCapabilities

newtype RscReleaseHook = RscReleaseHook { runReleaseHook :: IO () }

type UniqueStateTag = Type

newtype OptimiseM (s :: UniqueStateTag) a = OptimiseM {
      runOptimiseM :: SystemCapabilities -> IO (a, DList RscReleaseHook) }
  deriving (Functor)

instance Applicative (OptimiseM s) where
  pure x = OptimiseM . const $ pure (x, mempty)
  OptimiseM fs <*> OptimiseM xs
      = OptimiseM $ \cpbs -> do
          (f, fRscR) <- fs cpbs
          (x, xRscR) <- bracketOnError (pure())
                      (const $ forM_ (toList fRscR) runReleaseHook)
                      (const $ xs cpbs)
          return (f x, fRscR<>xRscR)
instance Monad (OptimiseM s) where
  return = pure
  OptimiseM xs >>= f = OptimiseM $ \cpbs -> do
     (x, xRscR) <- xs cpbs
     let OptimiseM ys = f x
     (y, yRscR) <- bracketOnError (pure())
                 (const $ forM_ (toList xRscR) runReleaseHook)
                 (const $ ys cpbs)
     return (y, xRscR<>yRscR)
instance MonadFail (OptimiseM s) where
  fail = OptimiseM . const . Control.Monad.Fail.fail

runWithCapabilities :: SystemCapabilities -> (∀ s . OptimiseM s a) -> a
runWithCapabilities cpbs (OptimiseM r) = unsafePerformIO $ do
    (res, rscRs) <- r cpbs
    forM_ (toList rscRs) runReleaseHook
    return res

unsafeIO :: IO a -> OptimiseM s a
unsafeIO = OptimiseM . const . fmap (,mempty)


class BatchOptimisable d where
  data Optimised d (s :: UniqueStateTag) (t :: Type->Type) :: Type
  allocateBatch :: Traversable t
      => t d -> OptimiseM s (Optimised d s t)
--traverseOptimisedT :: (Traversable t, MonadTrans f, Monad (f (OptimiseM s)))
--                        => (d -> f (OptimiseM s) y)
--                              -> Optimised d s t -> f (OptimiseM s) (t y)
--traverseOptimised :: (Traversable t)
--                        => (d -> OptimiseM s y)
--                              -> Optimised d s t -> OptimiseM s (t y)
--traverseOptimised f = runIdentityT . traverseOptimisedT (IdentityT . f)
  peekOptimised :: Traversable t
      => Optimised d s t -> OptimiseM s (t d)
  peekBatchShape :: Traversable t => Optimised d s t -> OptimiseM s (t ())
  peekBatchShape = fmap (fmap $ const ()) . peekOptimised
  optimiseBatch :: (Traversable t, BatchOptimisable d')
     => (Optimised d s t -> OptimiseM s (Optimised d' s t))
                -> t d -> OptimiseM s (t d')
  optimiseBatch f xs = OptimiseM $ \sysCaps -> do
      (xVals, xRscR) <- runOptimiseM (allocateBatch xs) sysCaps
      (yVals, yRscR) <- runOptimiseM (f xVals) sysCaps
      (peekd, _) <- runOptimiseM (peekOptimised yVals) sysCaps
      return (peekd, xRscR<>yRscR)

data VUOptimised a s t
    = VUOptimised { vuOptimisedShape :: t ()
                  , vuOptimisedVector :: VU.Vector a }

peekVUBatchShape :: VUOptimised a s t -> OptimiseM s (t ())
peekVUBatchShape = pure . vuOptimisedShape

peekVUOptimised :: (VU.Unbox a, Traversable t)
                      => VUOptimised a s t -> OptimiseM s (t a)
peekVUOptimised (VUOptimised shape vals)
        = pure . (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals `VU.unsafeIndex` i, i+1)

allocateVUBatch :: (VU.Unbox a, Traversable t)
           => t a -> OptimiseM s (VUOptimised a s t)
allocateVUBatch input = OptimiseM $ \_ -> do
      let n = Fldb.length input
      valV <- VUM.unsafeNew n
      shape <- (`evalStateT`0) . (`traverse`input) $ \x -> do
         i <- get
         VUM.unsafeWrite valV i x
         put $ i+1
         pure ()
      vals <- VU.unsafeFreeze valV
      return (VUOptimised shape vals, mempty)

instance BatchOptimisable Int where
  newtype Optimised Int s t
    = IntVectorOptim { getIntVUO :: VUOptimised Int s t }
  peekBatchShape = peekVUBatchShape . getIntVUO
  peekOptimised = peekVUOptimised . getIntVUO
  allocateBatch = fmap IntVectorOptim . allocateVUBatch

instance BatchOptimisable Double where
  newtype Optimised Double s t
    = DoubleVectorOptim { getDoubleVUO :: VUOptimised Double s t }
  peekBatchShape = peekVUBatchShape . getDoubleVUO
  peekOptimised = peekVUOptimised . getDoubleVUO
  allocateBatch = fmap DoubleVectorOptim . allocateVUBatch

instance ( Traversable t, QC.Arbitrary (t ())
         , QC.Arbitrary a, VU.Unbox a )
             => QC.Arbitrary (VUOptimised a s t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Fldb.length shape
     values <- replicateM n QC.arbitrary
     return $ VUOptimised shape (VU.fromList values)
  shrink = undefined

instance ( Traversable t, QC.Arbitrary (t ()) )
             => QC.Arbitrary (Optimised Int s t) where
  arbitrary = IntVectorOptim <$> QC.arbitrary
  shrink (IntVectorOptim v) = IntVectorOptim <$> QC.shrink v

instance ( Traversable t, QC.Arbitrary (t ()) )
             => QC.Arbitrary (Optimised Double s t) where
  arbitrary = DoubleVectorOptim <$> QC.arbitrary
  shrink (DoubleVectorOptim v) = DoubleVectorOptim <$> QC.shrink v

unsafeZipTraversablesWith :: Traversable t => (a -> b -> c)
                   -> t a -> t b -> t c
unsafeZipTraversablesWith f xs ys
             = (`SSM.evalState`Fldb.toList ys) . forM xs $ \x -> do
     y <- head <$> SSM.get
     SSM.modify tail
     return $ f x y

instance (BatchOptimisable a, BatchOptimisable b) => BatchOptimisable (a,b) where
  data Optimised (a,b) σ τ = OptimisedTuple
         { optimL :: Optimised a σ τ
         , optimR :: Optimised b σ τ }
  allocateBatch xys = do
    xos <- allocateBatch $ fst<$>xys
    yos <- allocateBatch $ snd<$>xys
    return $ OptimisedTuple xos yos
  peekOptimised (OptimisedTuple xos yos) = do
    xs <- peekOptimised xos
    ys <- peekOptimised yos
    return $ unsafeZipTraversablesWith (,) xs ys
