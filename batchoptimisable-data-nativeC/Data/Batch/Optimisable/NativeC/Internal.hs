-- |
-- Module      : Data.Batch.Optimisable.NativeC.Internal
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}


module Data.Batch.Optimisable.NativeC.Internal (
     module Data.Batch.Optimisable
   -- * Batch-packed data
   , CIntArray, CLongArray, CFloatArray, CDoubleArray
   ) where

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe

import Data.Kind(Type)
import Data.Traversable
import qualified Data.Foldable as Foldable
import GHC.TypeLits
import GHC.Exts (IsList(..))
import Data.Proxy

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VSM

import Control.Monad
import Control.Arrow (first)

import qualified Test.QuickCheck as QC

import System.IO.Unsafe
import Control.Monad.Primitive (PrimMonad, PrimState)
import Data.IORef
import qualified Language.C.Inline as C
import Data.Int
import Foreign.C.Types (CInt, CLong, CFloat, CDouble)
import Foreign (Ptr)

newtype MultiArray (dims :: [Nat]) t
  = MultiArray { getFlatIntArray :: VU.Vector t }
 deriving (Eq)

mapMArray :: (VU.Unbox a, VU.Unbox b, Monad f)
          => (a -> f b) -> MultiArray dims a -> f (MultiArray dims b)
mapMArray f (MultiArray v) = MultiArray <$> VU.mapM f v

nv :: ∀ n i . (KnownNat n, Integral i) => i
nv = fromInteger $ natVal (Proxy @n)

instance ∀ n t . (KnownNat n, VU.Unbox t)
        => IsList (MultiArray '[n] t) where
  type Item (MultiArray '[n] t) = t
  toList (MultiArray a) = VU.toList a
  fromList l
    | length l == n  = MultiArray $ VU.fromList l
   where n = nv @n

instance ∀ dims t . ( IsList (MultiArray dims t)
                    , Show (Item (MultiArray dims t) ) )
                   => Show (MultiArray dims t) where
  show = show . GHC.Exts.toList

transposeRep :: NonEmpty (NonEmpty a) -> NonEmpty (NonEmpty a)
transposeRep l = (NE.head <$> l)
     :| if Foldable.all (null . NE.tail) l
         then []
         else NE.toList . transposeRep $ fmap shTail l
 where shTail (h:|[]) = h:|[]
       shTail (_:|h:t) = h:|t


instance ∀ n t . (KnownNat n, VU.Unbox t, QC.Arbitrary t)
            => QC.Arbitrary (MultiArray '[n] t) where
  arbitrary = fromList <$> replicateM (nv @n)
                                      QC.arbitrary
  shrink (MultiArray a) = case VU.toList a of
       [] -> []
       l  -> MultiArray . VU.fromList . NE.toList <$>
                          NE.tail (transposeRep . NE.fromList
                                    $ zipWith (:|) l (QC.shrink<$>l))


type CIntArray n = MultiArray '[n] Int32
type CLongArray n = MultiArray '[n] Int
type CFloatArray n = MultiArray '[n] Float
type CDoubleArray n = MultiArray '[n] Double

C.context (C.baseCtx <> C.vecCtx)
C.include "<stdlib.h>"
C.include "<string.h>"

class VS.Storable c => CHandleable c where
  callocArray :: CInt -> IO (Ptr c)
  releaseArray :: Ptr c -> IO ()
  memcpyArray :: (Ptr c, CInt) -- ^ Target, with offset
              -> (Ptr c, CInt) -- ^ Source, with offset
              -> CInt          -- ^ Number of elements
              -> IO ()

class (VU.Unbox t, CHandleable (CCType t)) => CPortable t where
  type CCType t :: *
  thawForC :: PrimMonad m
    => VU.Vector t -> m (VSM.MVector (PrimState m) (CCType t))
  freezeFromC :: PrimMonad m
    => VSM.MVector (PrimState m) (CCType t) -> m (VU.Vector t)

instance CHandleable CInt where
  callocArray nElems = [C.exp| int* {calloc($(int nElems), sizeof(int))} |]
  releaseArray loc = [C.block| void { free ($(int* loc)); } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(int* tgt) + $(int tOffs)
                             , $(int* src) + $(int sOffs)
                             , $(int nElems) * sizeof(int)
                             ); } |]
instance CPortable Int32 where
  type CCType Int32 = CInt -- may be invalid on non-LinuxAMD64
  thawForC = VS.thaw . VS.map fromIntegral . VU.convert
  freezeFromC = fmap (VU.convert . VS.map fromIntegral) . VS.freeze

instance CHandleable CLong where
  callocArray nElems = [C.exp| long* {calloc($(int nElems), sizeof(long))} |]
  releaseArray loc = [C.block| void { free ($(long* loc)); } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(long* tgt) + $(int tOffs)
                             , $(long* src) + $(int sOffs)
                             , $(int nElems) * sizeof(long)
                             ); } |]
instance CPortable Int where
  type CCType Int = CLong -- may be invalid on non-LinuxAMD64
  thawForC = VS.thaw . VS.map fromIntegral . VU.convert
  freezeFromC = fmap (VU.convert . VS.map fromIntegral) . VS.freeze

instance CHandleable CFloat where
  callocArray nElems = [C.exp| float* {calloc($(int nElems), sizeof(float))} |]
  releaseArray loc = [C.block| void { free ($(float* loc)); } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(float* tgt) + $(int tOffs)
                             , $(float* src) + $(int sOffs)
                             , $(int nElems) * sizeof(float)
                             ); } |]
instance CPortable Float where
  type CCType Float = CFloat
  thawForC = VS.thaw . VS.map realToFrac . VU.convert
  freezeFromC = fmap (VU.convert . VS.map realToFrac) . VS.freeze

instance CHandleable CDouble where
  callocArray nElems = [C.exp| double* {calloc($(int nElems), sizeof(double))} |]
  releaseArray loc = [C.block| void { free ($(double* loc)); } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(double* tgt) + $(int tOffs)
                             , $(double* src) + $(int sOffs)
                             , $(int nElems) * sizeof(double)
                             ); } |]
instance CPortable Double where
  type CCType Double = CDouble
  thawForC = VS.thaw . VS.map realToFrac . VU.convert
  freezeFromC = fmap (VU.convert . VS.map realToFrac) . VS.freeze

instance ∀ n t . (KnownNat n, CPortable t)
              => BatchOptimisable (MultiArray '[n] t) where
  data Optimised (MultiArray '[n] t) s τ
            = OptdIntArr { oiaShape :: τ ()
                         , oiaLocation :: Ptr (CCType t) }
  allocateBatch input = OptimiseM $ \_ -> do
    let nArr = nv @n
        nBatch = Foldable.length input
        nElems = nArr * fromIntegral nBatch
    loc <- callocArray nElems
    iSt <- newIORef 0
    shp <- forM input $ \(MultiArray a) -> do
      i <- readIORef iSt
      -- doing two copies, but efficiency is not a concern here...
      aC <- thawForC a
      VSM.unsafeWith aC $ \aCP -> memcpyArray (loc, nArr*i) (aCP, 0) nArr
      modifyIORef iSt (+1)
      return ()
    return ( OptdIntArr shp loc
           , pure $ RscReleaseHook (releaseArray loc) )
  peekOptimised (OptdIntArr shp loc) = OptimiseM $ \_ -> do
    let nArr = nv @n
    tgt <- VSM.unsafeNew $ fromIntegral nArr
    iSt <- newIORef 0
    peekd <- forM shp $ \() -> do
      i <- readIORef iSt
      VSM.unsafeWith tgt $ \tgtP
            -> memcpyArray (tgtP, 0) (loc, nArr*i) nArr
      modifyIORef iSt (+1)
      MultiArray <$> freezeFromC tgt
    return (peekd, mempty)

