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
   , OptimiseM(..), runWithCapabilities, unsafeIO
   -- ** Batch containers
   , RATraversable(..), itraverse
   -- * System resource bookkeeping
   , SystemCapabilities
   , detectCpuCapabilities
   , RscReleaseHook(..)
   ) where

import Data.Kind(Type)
import Data.Traversable
import Control.Lens.Indexed (TraversableWithIndex(..))
import Data.Foldable as Foldable

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)

import Control.Monad
import Control.Monad.Fail
import Control.Monad.Trans.Identity
import Control.Monad.Trans.State.Strict as SSM
import Control.Monad.Trans.Class (MonadTrans(..))
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

class (TraversableWithIndex (IndexOf t) t, Hashable (IndexOf t), Eq (IndexOf t))
         => RATraversable t where
  type IndexOf t :: Type

instance RATraversable [] where
  type IndexOf [] = Int


class BatchOptimisable d where
  data Optimised d (s :: UniqueStateTag) (t :: Type->Type) :: Type
  allocateBatch :: RATraversable t
      => t d -> OptimiseM s (Optimised d s t)
--traverseOptimisedT :: (Traversable t, MonadTrans f, Monad (f (OptimiseM s)))
--                        => (d -> f (OptimiseM s) y)
--                              -> Optimised d s t -> f (OptimiseM s) (t y)
--traverseOptimised :: (Traversable t)
--                        => (d -> OptimiseM s y)
--                              -> Optimised d s t -> OptimiseM s (t y)
--traverseOptimised f = runIdentityT . traverseOptimisedT (IdentityT . f)
  peekOptimised :: RATraversable t
      => Optimised d s t -> OptimiseM s (t d)
  peekSingleSample :: RATraversable t
      => Optimised d s t -> IndexOf t -> OptimiseM s (Maybe d)
  optimiseBatch :: (RATraversable t, BatchOptimisable d')
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
                , intVecIndices :: HM.HashMap (IndexOf t) Int
                }
  peekOptimised (IntVector vals shape ixs)
        = pure . (`SSM.evalState`0) . (`traverse`shape)
         $ \() -> SSM.state $ \i -> (vals `VU.unsafeIndex` i, i+1)
  peekSingleSample (IntVector vals shape ixs) ix
        = pure . fmap (VU.unsafeIndex vals) $ HM.lookup ix ixs
--traverseOptimisedT f (IntVector vals shape _) = do
--    iSt <- lift . unsafeIO $ newIORef 0
--    forM shape $ \() -> do
--      i <- lift . unsafeIO $ do
--         i <- readIORef iSt
--         modifyIORef iSt (+1)
--         return i
--      f $ VU.unsafeIndex vals i
  allocateBatch input = OptimiseM $ \_ -> do
      let n = Foldable.length input
      valV <- VUM.unsafeNew n
      (shape, (_,ixs))
             <- (`runStateT`(0, HM.empty)) . (`itraverse`input) $ \ix x -> do
         (i, oldixs) <- get
         VUM.unsafeWrite valV i x
         put (i+1, HM.insert ix i oldixs)
         pure ()
      vals <- VU.unsafeFreeze valV
      return (IntVector vals shape ixs, mempty)

instance (RATraversable t, QC.Arbitrary (t ()))
             => QC.Arbitrary (Optimised Int s t) where
  arbitrary = do
     shape <- QC.arbitrary
     let n = Foldable.length shape
     values <- replicateM n QC.arbitrary
     let (_,ixs) = (`execState`(0,HM.empty)) . (`itraverse`shape) $ \ix () -> do
          (i, oldixs) <- get
          put (i+1, HM.insert ix i oldixs) 
          pure ()
     return $ IntVector (VU.fromList values) shape ixs
  shrink = undefined

