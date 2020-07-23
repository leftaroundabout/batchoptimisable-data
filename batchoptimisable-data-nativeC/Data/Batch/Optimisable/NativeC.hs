-- |
-- Module      : Data.Batch.Optimisable.NativeC
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


module Data.Batch.Optimisable.NativeC (
     module Data.Batch.Optimisable
   -- * Batch-packed data
   , CIntArray
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
import Data.IORef
import qualified Language.C.Inline as C
import Foreign.C.Types (CInt)
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


type CIntArray n = MultiArray '[n] Int

C.context (C.baseCtx <> C.vecCtx)
C.include "<stdlib.h>"
C.include "<string.h>"

instance ∀ n . (KnownNat n) => BatchOptimisable (MultiArray '[n] Int) where
  data Optimised (MultiArray '[n] Int) s t
            = OptdIntArr { oiaShape :: t ()
                         , oiaLocation :: Ptr CInt }
  allocateBatch input = OptimiseM $ \_ -> do
    let nArr = nv @n
        nBatch = Foldable.length input
        nElems = nArr * fromIntegral nBatch
    loc <- [C.exp| int* {calloc($(int nElems), sizeof(int))} |]
    let release = [C.block| void { free ($(int* loc)); } |]
    iSt <- newIORef 0
    shp <- forM input $ \(MultiArray a) -> do
      i <- readIORef iSt
      -- doing two copies, but efficiency is not a concern here...
      let aC = VS.map fromIntegral $ VS.convert a :: VS.Vector CInt
      [C.block| void { memcpy( $vec-ptr:(int* aC)
                             , $(int* loc) + $(int nArr) * $(int i)
                             , $(int nArr) * sizeof(int)
                             ); } |]
      modifyIORef iSt (+1)
      return ()
    return ( OptdIntArr shp loc
           , pure $ RscReleaseHook release )
  peekOptimised (OptdIntArr shp loc) = OptimiseM $ \_ -> do
    let nArr = nv @n
    tgt <- VSM.unsafeNew @IO @CInt $ fromIntegral nArr
    iSt <- newIORef 0
    peekd <- forM shp $ \() -> do
      i <- readIORef iSt
      [C.block| void { memcpy( $(int* loc) + $(int nArr) * $(int i)
                             , $vec-ptr:(int* tgt)
                             , $(int nArr) * sizeof(int)
                             ); } |]
      modifyIORef iSt (+1)
      MultiArray . VU.convert . VS.map fromIntegral <$> VS.freeze tgt
    return (peekd, mempty)

