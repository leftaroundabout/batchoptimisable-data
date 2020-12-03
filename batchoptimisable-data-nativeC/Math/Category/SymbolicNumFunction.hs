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

  SymbUnaryElementary :: SymbNumUnaryElementaryFn a -> SymbNumFn ζ a a
  SymbBinaryElementary :: SymbNumBinaryElementaryFn a -> SymbNumFn ζ (a,a) a
  SymbMul :: VectorSpace v => SymbNumFn ζ (Scalar v, v) v
  SymbInnerProd :: (InnerSpace v, ζ v) => SymbNumFn ζ (v, v) (Scalar v)
  SymbDiv :: (VectorSpace v, Fractional (Scalar v))
                  => SymbNumFn ζ (v, Scalar v) v


data SymbNumUnaryElementaryFn a where
  SymbNegate :: AdditiveGroup a => SymbNumUnaryElementaryFn a
  SymbAbs, SymbRelu, SymbSignum :: Num a => SymbNumUnaryElementaryFn a
  SymbRecip :: Fractional a => SymbNumUnaryElementaryFn a
  SymbElementaryFloating
     :: Floating a => SymbElementaryFlFn a -> SymbNumUnaryElementaryFn a

data SymbElementaryFlFn :: Type -> Type where
  SymbExp, SymbLog, SymbSqrt, SymbSin, SymbCos, SymbTan, SymbAsin, SymbAcos
   , SymbAtan, SymbSinh, SymbCosh, SymbTanh, SymbAsinh, SymbAcosh, SymbAtanh
      :: SymbElementaryFlFn a

data SymbNumBinaryElementaryFn a where
  SymbAdd, SymbSubtract :: AdditiveGroup a => SymbNumBinaryElementaryFn a
  SymbPow :: Floating a => SymbNumBinaryElementaryFn a
  SymbLogBase :: Floating a => SymbNumBinaryElementaryFn a


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
  (^+^) = genericAgentCombine (SymbBinaryElementary SymbAdd)
  (^-^) = genericAgentCombine (SymbBinaryElementary SymbSubtract)
  negateV = genericAgentMap (SymbUnaryElementary SymbNegate)

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
  abs = genericAgentMap (SymbUnaryElementary SymbAbs)
  signum = genericAgentMap (SymbUnaryElementary SymbSignum)

instance (VectorSpace n, Fractional n, n ~ Scalar n, ζ (), ζ n)
            => Fractional (SymbNumVal ζ a n) where
  fromRational = point . fromRational
  recip = genericAgentMap (SymbUnaryElementary SymbRecip)
  (/) = genericAgentCombine SymbDiv

floatingAgentMap :: (VectorSpace n, Floating n, n ~ Scalar n, ζ (), ζ n)
     => SymbElementaryFlFn n -> SymbNumVal ζ a n -> SymbNumVal ζ a n
floatingAgentMap = genericAgentMap . SymbUnaryElementary . SymbElementaryFloating

instance (VectorSpace n, Floating n, n ~ Scalar n, ζ (), ζ n)
            => Floating (SymbNumVal ζ a n) where
  pi = point pi
  logBase = genericAgentCombine (SymbBinaryElementary SymbLogBase)
  exp = floatingAgentMap SymbExp
  log = floatingAgentMap SymbLog
  sqrt = floatingAgentMap SymbSqrt
  sin = floatingAgentMap SymbSin
  cos = floatingAgentMap SymbCos
  tan = floatingAgentMap SymbTan
  sinh = floatingAgentMap SymbSinh
  cosh = floatingAgentMap SymbCosh
  tanh = floatingAgentMap SymbTanh
  asin = floatingAgentMap SymbAsin
  acos = floatingAgentMap SymbAcos
  atan = floatingAgentMap SymbAtan
  asinh = floatingAgentMap SymbAsinh
  acosh = floatingAgentMap SymbAcosh
  atanh = floatingAgentMap SymbAtanh


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

  arr SymbMul (μ,v) = μ*^v
  arr SymbInnerProd (v,w) = v<.>w
  arr SymbDiv (x,y) = x^/y

  arr (SymbUnaryElementary f) x = case f of
    SymbAbs -> abs x
    SymbNegate -> negateV x
    SymbRelu -> 2*abs x - x
    SymbSignum -> signum x
    SymbRecip -> recip x
    SymbElementaryFloating 𝑓 -> case 𝑓 of
       SymbExp -> exp x
       SymbLog -> log x
       SymbSqrt -> sqrt x
       SymbSin -> sin x
       SymbCos -> cos x
       SymbTan -> tan x
       SymbAsin -> asin x
       SymbAcos -> acos x
       SymbAtan -> atan x
       SymbSinh -> sinh x
       SymbCosh -> cosh x
       SymbTanh -> tanh x
       SymbAsinh -> asinh x
       SymbAcosh -> acosh x
       SymbAtanh -> atanh x
      
  arr (SymbBinaryElementary f) (x,y) = case f of
     SymbAdd -> x^+^y
     SymbSubtract -> x^-^y
     SymbLogBase -> logBase x y
     SymbPow -> x**y

