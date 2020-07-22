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
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables  #-}


module Data.Batch.Optimisable.NativeC (
     module Data.Batch.Optimisable
   -- * Batch-packed data
   , CIntArray
   ) where

import Data.Batch.Optimisable

import Data.Kind(Type)
import Data.Traversable
import qualified Data.Foldable as Foldable
import GHC.TypeLits
import GHC.Exts (IsList(..))
import Data.Proxy

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

import Control.Monad
import Control.Arrow (first)

import qualified Test.QuickCheck as QC

import System.IO.Unsafe

newtype MultiArray (dims :: [Nat]) t
  = MultiArray { getFlatIntArray :: VU.Vector t }
 deriving (Eq)

mapMArray :: (VU.Unbox a, VU.Unbox b, Monad f)
          => (a -> f b) -> MultiArray dims a -> f (MultiArray dims b)
mapMArray f (MultiArray v) = MultiArray <$> VU.mapM f v

instance ∀ n t . (KnownNat n, VU.Unbox t)
        => IsList (MultiArray '[n] t) where
  type Item (MultiArray '[n] t) = t
  toList (MultiArray a) = VU.toList a
  fromList l
    | length l == n  = MultiArray $ VU.fromList l
   where n = fromInteger $ natVal (Proxy @n)

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
  arbitrary = fromList <$> replicateM (fromInteger $ natVal (Proxy @n))
                                      QC.arbitrary
  shrink (MultiArray a) = case VU.toList a of
       [] -> []
       l  -> MultiArray . VU.fromList . NE.toList <$>
                          NE.tail (transposeRep . NE.fromList
                                    $ zipWith (:|) l (QC.shrink<$>l))


type CIntArray n = MultiArray '[n] Int


instance (KnownNat n) => BatchOptimisable (MultiArray '[n] Int) where
  newtype Optimised (MultiArray '[n] Int) s t
            = PseudoOptdIntArr (t (MultiArray '[n] Int))
  allocateBatch = pure . PseudoOptdIntArr
  peekOptimised (PseudoOptdIntArr a) = pure a

