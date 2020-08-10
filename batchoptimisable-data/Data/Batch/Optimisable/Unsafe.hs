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
   , detectCpuCapabilities
   , RscReleaseHook(..)
   -- * Utility
   , unsafeZipTraversablesWith
   ) where

import Data.Kind(Type)
import Data.Traversable
import Control.Lens.Indexed (TraversableWithIndex(..))
import Data.Foldable as Fldb

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

instance BatchOptimisable Int where
  data Optimised Int s t
    = IntVector { getIntVector :: VU.Vector Int
                , intVecShape :: t ()
                }
  peekBatchShape = pure . intVecShape
  peekOptimised (IntVector vals shape)
        = pure . (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals `VU.unsafeIndex` i, i+1)
--traverseOptimisedT f (IntVector vals shape _) = do
--    iSt <- lift . unsafeIO $ newIORef 0
--    forM shape $ \() -> do
--      i <- lift . unsafeIO $ do
--         i <- readIORef iSt
--         modifyIORef iSt (+1)
--         return i
--      f $ VU.unsafeIndex vals i
  allocateBatch input = OptimiseM $ \_ -> do
      let n = Fldb.length input
      valV <- VUM.unsafeNew n
      shape <- (`evalStateT`0) . (`traverse`input) $ \x -> do
         i <- get
         VUM.unsafeWrite valV i x
         put $ i+1
         pure ()
      vals <- VU.unsafeFreeze valV
      return (IntVector vals shape, mempty)

instance (Traversable t, QC.Arbitrary (t ()))
             => QC.Arbitrary (Optimised Int s t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Fldb.length shape
     values <- replicateM n QC.arbitrary
     return $ IntVector (VU.fromList values) shape
  shrink = undefined

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
