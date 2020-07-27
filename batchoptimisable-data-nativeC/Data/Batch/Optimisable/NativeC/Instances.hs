-- |
-- Module      : Data.Batch.Optimisable.NativeC.Instances
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


module Data.Batch.Optimisable.NativeC.Instances () where

import Data.Batch.Optimisable.NativeC.Internal

import Data.AffineSpace
import Data.AdditiveGroup
import Data.VectorSpace
import Math.Manifold.Core.PseudoAffine

import qualified Data.Vector.Unboxed as VU

import GHC.TypeLits (KnownNat)


instance (Fractional t, VU.Unbox t) => Fractional (MultiArray '[] t) where
  fromRational = constArray . fromRational
  recip = mapArray recip
  (/) = zipArrayWith (/)

instance (Floating t, VU.Unbox t) => Floating (MultiArray '[] t) where
  pi = constArray pi
  exp = mapArray exp
  log = mapArray log
  sin = mapArray sin
  cos = mapArray cos
  asin = mapArray asin
  acos = mapArray acos
  atan = mapArray atan
  sinh = mapArray sinh
  cosh = mapArray cosh
  asinh = mapArray asinh
  acosh = mapArray acosh
  atanh = mapArray atanh
  tan = mapArray tan
  logBase = zipArrayWith logBase

instance (Real t, VU.Unbox t) => Real (MultiArray '[] t) where
  toRational (MultiArray a) = toRational $ VU.head a

instance (RealFrac t, VU.Unbox t) => RealFrac (MultiArray '[] t) where
  properFraction (MultiArray a) = case properFraction $ VU.head a of
       (b, r) -> (b, constArray r)

instance (Enum t, VU.Unbox t) => Enum (MultiArray '[] t) where
  fromEnum (MultiArray s) = fromEnum $ VU.head s
  toEnum = MultiArray . VU.singleton . toEnum
  enumFromThenTo (MultiArray s) (MultiArray n) (MultiArray t)
     = MultiArray . VU.singleton
         <$> enumFromThenTo (VU.head s) (VU.head n) (VU.head t)

instance (Integral t, VU.Unbox t) => Integral (MultiArray '[] t) where
  quotRem (MultiArray n) (MultiArray d)
       = case quotRem (VU.head n) (VU.head d) of
            (q,r) -> (constArray q, constArray r)
  toInteger (MultiArray n) = toInteger $ VU.head n

instance ∀ t dims .
      (Semimanifold t, VU.Unbox t, VU.Unbox (Needle t), KnownShape dims)
              => Semimanifold (MultiArray dims t) where
  type Needle (MultiArray dims t) = MultiArray dims (Needle t)
  semimanifoldWitness = case semimanifoldWitness @t of
     SemimanifoldWitness -> SemimanifoldWitness
  (.+~^) = zipArrayWith (.+~^)

instance ∀ t dims .
      (PseudoAffine t, VU.Unbox t, VU.Unbox (Needle t), KnownShape dims)
              => PseudoAffine (MultiArray dims t) where
  pseudoAffineWitness = case pseudoAffineWitness @t of
    PseudoAffineWitness SemimanifoldWitness
      -> PseudoAffineWitness SemimanifoldWitness
  (.-~!) = zipArrayWith (.-~!)

instance (AffineSpace t, VU.Unbox t, VU.Unbox (Diff t), KnownShape dims)
              => AffineSpace (MultiArray dims t) where
  type Diff (MultiArray dims t) = MultiArray dims (Diff t)
  (.-.) = zipArrayWith (.-.)
  (.+^) = zipArrayWith (.+^)

instance (AdditiveGroup t, VU.Unbox t, KnownShape dims)
              => AdditiveGroup (MultiArray dims t) where
  zeroV = constArray zeroV
  negateV = mapArray negateV
  (^+^) = zipArrayWith (^+^)

instance (VectorSpace t, VU.Unbox t, KnownShape dims)
              => VectorSpace (MultiArray dims t) where
  type Scalar (MultiArray dims t) = Scalar t
  μ*^v = mapArray (μ*^) v

instance (InnerSpace t, VU.Unbox t, KnownShape dims, Num (Scalar t))
              => InnerSpace (MultiArray dims t) where
  MultiArray v<.>MultiArray w
    = VU.ifoldl' (\acc i vi -> acc + vi<.>VU.unsafeIndex w i) 0 v
