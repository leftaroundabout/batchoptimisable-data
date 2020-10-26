-- |
-- Module      : Math.Category.SymbolicNumFn
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
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE UnicodeSyntax         #-}

module Math.Category.SymbolicNumFn where

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AdditiveGroup
import Data.VectorSpace

import Data.Kind (Type)


data SymbNumFn :: Type -> Type -> Type where
  SymbConst :: c -> SymbNumFn a c
  SymbId :: SymbNumFn a a

  SymbCompo :: SymbNumFn b c -> SymbNumFn a b -> SymbNumFn a c
  SymbPar :: SymbNumFn a b -> SymbNumFn α β -> SymbNumFn (a,α) (b,β)
  SymbCopy :: SymbNumFn a (a,a)
  SymbSwap :: SymbNumFn (a,b) (b,a)
  SymbRegroup :: SymbNumFn (a,(b,c)) ((a,b),c)
  SymbRegroup' :: SymbNumFn ((a,b),c) (a,(b,c))
  SymbFst :: SymbNumFn (a,b) a
  SymbSnd :: SymbNumFn (a,b) b

  SymbNegate :: AdditiveGroup a => SymbNumFn a a
  SymbAdd :: AdditiveGroup a => SymbNumFn (a,a) a
  SymbMul :: VectorSpace v => SymbNumFn (Scalar v, v) v
  SymbInnerProd :: InnerSpace v => SymbNumFn (v, v) (Scalar v)

  SymbAbs :: Num a => SymbNumFn a a
  SymbRelu :: Num a => SymbNumFn a a

  SymbRecip :: Fractional a => SymbNumFn a a
  SymbDiv :: (VectorSpace v, Fractional (Scalar v))
                  => SymbNumFn (v, Scalar v) v

  SymbExp :: Floating a => SymbNumFn a a
  SymbLog :: Floating a => SymbNumFn a a
  SymbLogBase :: Floating a => SymbNumFn (a,a) a
  SymbSqrt :: Floating a => SymbNumFn a a
  SymbPow :: Floating a => SymbNumFn (a,a) a

  SymbSin :: Floating a => SymbNumFn a a
  SymbCos :: Floating a => SymbNumFn a a
  SymbTan :: Floating a => SymbNumFn a a
  SymbAsin :: Floating a => SymbNumFn a a
  SymbAcos :: Floating a => SymbNumFn a a
  SymbAtan :: Floating a => SymbNumFn a a
  SymbSinh :: Floating a => SymbNumFn a a
  SymbCosh :: Floating a => SymbNumFn a a
  SymbTanh :: Floating a => SymbNumFn a a
  SymbAsinh :: Floating a => SymbNumFn a a
  SymbAcosh :: Floating a => SymbNumFn a a
  SymbAtanh :: Floating a => SymbNumFn a a


instance Category SymbNumFn where
  id = SymbId
  (.) = SymbCompo

instance Cartesian SymbNumFn where
  swap = SymbSwap
  attachUnit = id &&& terminal
  detachUnit = fst
  regroup = SymbRegroup
  regroup' = SymbRegroup'

instance Morphism SymbNumFn where
  (***) = SymbPar

instance PreArrow SymbNumFn where
  f&&&g = (f***g) . SymbCopy
  terminal = SymbConst ()
  fst = SymbFst
  snd = SymbSnd

instance WellPointed SymbNumFn where
  const = SymbConst
  unit = pure ()

type SymbNumVal = GenericAgent SymbNumFn

instance HasAgent SymbNumFn where
  type AgentVal SymbNumFn a v = SymbNumVal a v
  alg = genericAlg
  ($~) = genericAgentMap

instance CartesianAgent SymbNumFn where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2

instance PointAgent SymbNumVal SymbNumFn a x where
  point = genericPoint



