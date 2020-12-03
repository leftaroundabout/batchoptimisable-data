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

  SymbPow :: Floating a => SymbNumFn ζ (a,a) a
  SymbLogBase :: Floating a => SymbNumFn ζ (a,a) a

  SymbElementaryFloating :: Floating a => SymbElementaryFlFn a a -> SymbNumFn ζ a a

data SymbElementaryFlFn :: Type -> Type -> Type where
  SymbExp, SymbLog, SymbSqrt, SymbSin, SymbCos, SymbTan, SymbAsin, SymbAcos
   , SymbAtan, SymbSinh, SymbCosh, SymbTanh, SymbAsinh, SymbAcosh, SymbAtanh
      :: SymbElementaryFlFn a a


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
  logBase = genericAgentCombine SymbLogBase
  exp = genericAgentMap $ SymbElementaryFloating SymbExp
  log = genericAgentMap $ SymbElementaryFloating SymbLog
  sqrt = genericAgentMap $ SymbElementaryFloating SymbSqrt
  sin = genericAgentMap $ SymbElementaryFloating SymbSin
  cos = genericAgentMap $ SymbElementaryFloating SymbCos
  tan = genericAgentMap $ SymbElementaryFloating SymbTan
  sinh = genericAgentMap $ SymbElementaryFloating SymbSinh
  cosh = genericAgentMap $ SymbElementaryFloating SymbCosh
  tanh = genericAgentMap $ SymbElementaryFloating SymbTanh
  asin = genericAgentMap $ SymbElementaryFloating SymbAsin
  acos = genericAgentMap $ SymbElementaryFloating SymbAcos
  atan = genericAgentMap $ SymbElementaryFloating SymbAtan
  asinh = genericAgentMap $ SymbElementaryFloating SymbAsinh
  acosh = genericAgentMap $ SymbElementaryFloating SymbAcosh
  atanh = genericAgentMap $ SymbElementaryFloating SymbAtanh


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

  arr SymbLogBase (b,e) = logBase b e
  arr SymbPow (x,y) = x**y

  arr (SymbElementaryFloating SymbExp) x = exp x
  arr (SymbElementaryFloating SymbLog) x = log x
  arr (SymbElementaryFloating SymbSqrt) x = sqrt x

  arr (SymbElementaryFloating SymbSin) x = sin x
  arr (SymbElementaryFloating SymbCos) x = cos x
  arr (SymbElementaryFloating SymbTan) x = tan x
  arr (SymbElementaryFloating SymbAsin) x = asin x
  arr (SymbElementaryFloating SymbAcos) x = acos x
  arr (SymbElementaryFloating SymbAtan) x = atan x
  arr (SymbElementaryFloating SymbSinh) x = sinh x
  arr (SymbElementaryFloating SymbCosh) x = cosh x
  arr (SymbElementaryFloating SymbTanh) x = tanh x
  arr (SymbElementaryFloating SymbAsinh) x = asinh x
  arr (SymbElementaryFloating SymbAcosh) x = acosh x
  arr (SymbElementaryFloating SymbAtanh) x = atanh x
