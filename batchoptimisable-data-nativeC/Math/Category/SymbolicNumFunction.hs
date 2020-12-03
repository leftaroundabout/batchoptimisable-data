-- |
-- Module      : Math.Category.SymbolicNumFunction
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE UnicodeSyntax         #-}

module Math.Category.SymbolicNumFunction where

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AdditiveGroup
import Data.VectorSpace

import Data.Kind (Type)
import GHC.Exts (Constraint)


data SymbNumFn :: (Type -> Constraint) -> Type -> Type -> Type where
  SymbConst :: ζ c => c -> SymbNumFn ζ a c
  SymbId :: SymbNumFn ζ a a

  SymbCompo :: SymbNumFn ζ b c -> SymbNumFn ζ a b -> SymbNumFn ζ a c
  SymbPar :: SymbNumFn ζ a b -> SymbNumFn ζ α β -> SymbNumFn ζ (a,α) (b,β)
  SymbCopy :: SymbNumFn ζ a (a,a)
  SymbSwap :: SymbNumFn ζ (a,b) (b,a)
  SymbRegroup :: SymbNumFn ζ (a,(b,c)) ((a,b),c)
  SymbRegroup' :: SymbNumFn ζ ((a,b),c) (a,(b,c))
  SymbFst :: SymbNumFn ζ (a,b) a
  SymbSnd :: SymbNumFn ζ (a,b) b

  SymbNegate :: AdditiveGroup a => SymbNumFn ζ a a
  SymbAdd :: AdditiveGroup a => SymbNumFn ζ (a,a) a
  SymbSubtract :: AdditiveGroup a => SymbNumFn ζ (a,a) a
  SymbMul :: VectorSpace v => SymbNumFn ζ (Scalar v, v) v
  SymbInnerProd :: (InnerSpace v, ζ v) => SymbNumFn ζ (v, v) (Scalar v)

  SymbAbs :: Num a => SymbNumFn ζ a a
  SymbRelu :: Num a => SymbNumFn ζ a a
  SymbSignum :: Num a => SymbNumFn ζ a a

  SymbRecip :: Fractional a => SymbNumFn ζ a a
  SymbDiv :: (VectorSpace v, Fractional (Scalar v))
                  => SymbNumFn ζ (v, Scalar v) v

  SymbExp, SymbLog :: Floating a => SymbNumFn ζ a a
  -- SymbLog :: Floating a => SymbNumFn ζ a a
  SymbLogBase :: Floating a => SymbNumFn ζ (a,a) a
  SymbSqrt :: Floating a => SymbNumFn ζ a a
  SymbPow :: Floating a => SymbNumFn ζ (a,a) a

  SymbSin :: Floating a => SymbNumFn ζ a a
  SymbCos :: Floating a => SymbNumFn ζ a a
  SymbTan :: Floating a => SymbNumFn ζ a a
  SymbAsin :: Floating a => SymbNumFn ζ a a
  SymbAcos :: Floating a => SymbNumFn ζ a a
  SymbAtan :: Floating a => SymbNumFn ζ a a
  SymbSinh :: Floating a => SymbNumFn ζ a a
  SymbCosh :: Floating a => SymbNumFn ζ a a
  SymbTanh :: Floating a => SymbNumFn ζ a a
  SymbAsinh :: Floating a => SymbNumFn ζ a a
  SymbAcosh :: Floating a => SymbNumFn ζ a a
  SymbAtanh :: Floating a => SymbNumFn ζ a a


instance Category (SymbNumFn ζ) where
  id = SymbId
  (.) = SymbCompo

instance ζ () => Cartesian (SymbNumFn ζ) where
  swap = SymbSwap
  attachUnit = id &&& terminal
  detachUnit = fst
  regroup = SymbRegroup
  regroup' = SymbRegroup'

instance ζ () => Morphism (SymbNumFn ζ) where
  (***) = SymbPar

instance ζ () => PreArrow (SymbNumFn ζ) where
  f&&&g = SymbCompo (SymbPar f g) SymbCopy
  terminal = SymbConst ()
  fst = SymbFst
  snd = SymbSnd

instance ζ () => WellPointed (SymbNumFn ζ) where
  type PointObject (SymbNumFn ζ) o = ζ o
  const = SymbConst
  unit = pure ()

type SymbNumVal ζ = GenericAgent (SymbNumFn ζ)

instance HasAgent (SymbNumFn ζ) where
  type AgentVal (SymbNumFn ζ) a v = SymbNumVal ζ a v
  alg = genericAlg
  ($~) = genericAgentMap

instance ζ () => CartesianAgent (SymbNumFn ζ) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2

instance (ζ (), ζ x) => PointAgent (SymbNumVal ζ) (SymbNumFn ζ) a x where
  point = genericPoint


instance (AdditiveGroup x, ζ (), ζ x) => AdditiveGroup (SymbNumVal ζ a x) where
  zeroV = point zeroV
  (^+^) = genericAgentCombine SymbAdd
  (^-^) = genericAgentCombine SymbSubtract
  negateV = genericAgentMap SymbNegate

instance (VectorSpace v, ζ (), ζ v) => VectorSpace (SymbNumVal ζ a v) where
  type Scalar (SymbNumVal ζ a v) = SymbNumVal ζ a (Scalar v)
  (*^) = genericAgentCombine SymbMul

instance (VectorSpace n, Num n, n ~ Scalar n, ζ (), ζ n)
            => Num (SymbNumVal ζ a n) where
  fromInteger = point . fromInteger
  (+) = (^+^)
  (-) = (^-^)
  (*) = (*^)
  negate = negateV
  abs = genericAgentMap SymbAbs
  signum = genericAgentMap SymbSignum

instance (VectorSpace n, Fractional n, n ~ Scalar n, ζ (), ζ n)
            => Fractional (SymbNumVal ζ a n) where
  fromRational = point . fromRational
  (/) = genericAgentCombine SymbDiv

instance (VectorSpace n, Floating n, n ~ Scalar n, ζ (), ζ n)
            => Floating (SymbNumVal ζ a n) where
  pi = point pi
  exp = genericAgentMap SymbExp
  log = genericAgentMap SymbLog
  logBase = genericAgentCombine SymbLogBase
  sqrt = genericAgentMap SymbSqrt
  sin = genericAgentMap SymbSin
  cos = genericAgentMap SymbCos
  tan = genericAgentMap SymbTan
  sinh = genericAgentMap SymbSinh
  cosh = genericAgentMap SymbCosh
  tanh = genericAgentMap SymbTanh
  asin = genericAgentMap SymbAsin
  acos = genericAgentMap SymbAcos
  atan = genericAgentMap SymbAtan
  asinh = genericAgentMap SymbAsinh
  acosh = genericAgentMap SymbAcosh
  atanh = genericAgentMap SymbAtanh


instance EnhancedCat (->) (SymbNumFn ζ) where
  arr (SymbConst c) _ = c
  arr SymbId x = x

  arr (SymbCompo f g) x = (arr f . arr g) x
  arr (SymbPar f g) (x,y) = (f$x, g$y)
  arr SymbCopy x = (x,x)
  arr SymbSwap (x,y) = (y,x)
  arr SymbRegroup (x,(y,z)) = ((x,y),z)
  arr SymbRegroup' ((x,y),z) = (x,(y,z))
  arr SymbFst (x,_) = x
  arr SymbSnd (_,y) = y

  arr SymbNegate x = negateV x
  arr SymbAdd (x,y) = x^+^y
  arr SymbSubtract (x,y) = x^-^y
  arr SymbMul (μ,v) = μ*^v
  arr SymbInnerProd (v,w) = v<.>w

  arr SymbAbs x = abs x
  arr SymbRelu x = 2*abs x - x
  arr SymbSignum x = signum x

  arr SymbRecip x = recip x
  arr SymbDiv (x,y) = x^/y

  arr SymbExp x = exp x
  arr SymbLog x = log x
  arr SymbLogBase (b,e) = logBase b e
  arr SymbSqrt x = sqrt x
  arr SymbPow (x,y) = x**y

  arr SymbSin x = sin x
  arr SymbCos x = cos x
  arr SymbTan x = tan x
  arr SymbAsin x = asin x
  arr SymbAcos x = acos x
  arr SymbAtan x = atan x
  arr SymbSinh x = sinh x
  arr SymbCosh x = cosh x
  arr SymbTanh x = tanh x
  arr SymbAsinh x = asinh x
  arr SymbAcosh x = acosh x
  arr SymbAtanh x = atanh x
