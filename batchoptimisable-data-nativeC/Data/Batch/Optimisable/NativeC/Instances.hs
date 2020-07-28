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
import Math.LinearMap.Category

import qualified Data.Vector.Unboxed as VU

import GHC.TypeLits (KnownNat)
import Data.Kind (Type)
import Data.Type.Coercion


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

type family (++) (l :: [k]) (m :: [k]) :: [k] where
  '[] ++ m = m
  (h ': t) ++ m = h ': (t++m)

placeAtIndex :: ∀ dims w . (KnownShape dims, AdditiveGroup w, VU.Unbox w)
                    => Int -> w -> MultiArray dims w
placeAtIndex i w = MultiArray
   $ VU.replicate i zeroV <> VU.singleton w <> VU.replicate (n-i-1) zeroV
 where n = product $ shape @dims

allIndices :: ∀ dims . KnownShape dims => [Int]
allIndices = [0 .. product (shape @dims) - 1]

--type family MATensorProduct dims t w where
--  MATensorProduct dims t t = MultiArray dims t
--  MATensorProduct dims t (MultiArray dims' t) = MultiArray (dims++dims') t
type MATensorProduct dims t e = [t⊗e]

instance ∀ t dims . ( TensorSpace t, VU.Unbox t, t ~ Needle t
                    , KnownShape dims, Num (Scalar t) )
     => TensorSpace (MultiArray dims t) where
  type TensorProduct (MultiArray dims t) w = MATensorProduct dims t w
  addTensors (Tensor t) (Tensor u)
      = Tensor $ zipWith (^+^) t u
  subtractTensors (Tensor t) (Tensor u)
      = Tensor $ zipWith (^-^) t u
  scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ map (μ*^) t
  negateTensor = LinearFunction $ \(Tensor t) -> Tensor $ map negateV t
  wellDefinedVector (MultiArray a)
      = MultiArray <$> VU.mapM wellDefinedVector a
  scalarSpaceWitness = case scalarSpaceWitness @t of
       ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness @t of
       LinearManifoldWitness -> LinearManifoldWitness
  zeroTensor = Tensor $ replicate (product $ shape @dims) zeroV
  toFlatTensor = LinearFunction $ \(MultiArray a)
       -> Tensor $ getLinearFunction toFlatTensor <$> VU.toList a
  fromFlatTensor = LinearFunction $ \(Tensor t)
       -> MultiArray . VU.fromList $ getLinearFunction fromFlatTensor<$>t
  tensorProduct = bilinearFunction $
       \(MultiArray a) w -> Tensor [ (tensorProduct -+$> ai) -+$> w
                                   | ai <- VU.toList a ]
  transposeTensor = LinearFunction $
       \(Tensor t) -> sumV
           [ (fmapTensor -+$> LinearFunction (placeAtIndex i))
                -+$> transposeTensor -+$> tw
           | (i, tw) <- zip [0..] t ]
   where n = product $ shape @dims
  fmapTensor = bilinearFunction $ \f (Tensor t)
      -> Tensor $ getLinearFunction (fmapTensor-+$>f)<$>t
  fzipTensorWith = bilinearFunction $
      \f (Tensor mtw, Tensor mtx) -> Tensor $ zipWith
          (\tw tx -> (fzipTensorWith-+$>f)-+$>(tw,tx)) mtw mtx
  coerceFmapTensorProduct _ c
       = case coerceFmapTensorProduct @t [] c of
           Coercion -> Coercion
  wellDefinedTensor (Tensor t) = Tensor <$> mapM wellDefinedTensor t


instance ∀ t dims . ( LinearSpace t, t ~ Needle t
                    , VU.Unbox t, VU.Unbox (DualVector t)
                    , KnownShape dims
                    , Num (Scalar t), VU.Unbox (Scalar t) )
     => LinearSpace (MultiArray dims t) where
  type DualVector (MultiArray dims t) = MultiArray dims (DualVector t)
  dualSpaceWitness = case dualSpaceWitness @t of
      DualSpaceWitness -> case linearManifoldWitness @(DualVector t) of
         LinearManifoldWitness -> DualSpaceWitness
  linearId = case dualSpaceWitness @t of
      DualSpaceWitness ->
             LinearMap [ (fmapTensor-+$>LinearFunction`id`
                           placeAtIndex @dims i )
                          -+$>Tensor(getLinearMap $ linearId @t)
                       | i <- allIndices @dims
                       ]
  applyDualVector = bilinearFunction $
      \(MultiArray d) (MultiArray v)
         -> VU.sum $ VU.zipWith ((-+$>).(applyDualVector-+$>)) d v
  applyLinear = bilinearFunction $
      \(LinearMap f) (MultiArray v)
         -> sumV [ (applyLinear @t -+$> LinearMap q) -+$> (v VU.! i)
                 | (i, Tensor q) <- zip [0..] f ]
  tensorId = tid
   where tid :: ∀ w . (LinearSpace w, Scalar w ~ Scalar t)
             => (MultiArray dims t ⊗ w) +> (MultiArray dims t ⊗ w)
         tid = case (dualSpaceWitness @t, dualSpaceWitness @w) of
          (DualSpaceWitness, DualSpaceWitness) -> LinearMap
           [ (fmapTensor -+$> fmapTensor -+$> LinearFunction`id`
                \t -> Tensor $ replicate i zeroV
                                <> [t]
                                <> replicate (n-i-1) zeroV )
                 -+$>(Tensor (getLinearMap (tensorId :: (t⊗w)+>(t⊗w)))
                        :: DualVector t⊗(DualVector w ⊗ (t⊗w)) )
           | i <- allIndices @dims ]
         n = product $ shape @dims
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) (Tensor ttu)
      -> sum $ zipWith (\(Tensor tu') tu ->
                   (applyTensorFunctional-+$>LinearMap tu')-+$>tu)
                                      f ttu
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) (Tensor ttu)
      -> sumV $ zipWith (\(Tensor tuw) tu ->
                   (applyTensorLinMap-+$>LinearMap tuw)-+$>tu ) f ttu
