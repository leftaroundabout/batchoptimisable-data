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
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE UnicodeSyntax         #-}

module Math.Category.SymbolicNumFunction where

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AdditiveGroup
import Data.VectorSpace

import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(Refl))
import Data.Kind (Type)
import GHC.Exts (Constraint)


data SymbNumFn :: (Type -> Constraint) -> Type -> Type -> Type where
  SymbConst :: (ζ c, Typeable c, Eq c) => c -> SymbNumFn ζ a c
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
  SymbScalarMul :: VectorSpace v => SymbNumFn ζ (v, Scalar v) v
  SymbScalarDiv :: (VectorSpace v, Fractional (Scalar v))
                  => SymbNumFn ζ (v, Scalar v) v
  SymbInnerProd :: (InnerSpace v, ζ v) => SymbNumFn ζ (v, v) (Scalar v)

deriving instance Show (SymbNumFn Show a b)

data SymbNumUnaryElementaryFn a where
  SymbNegate :: AdditiveGroup a => SymbNumUnaryElementaryFn a
  SymbAbs, SymbRelu, SymbSignum :: Num a => SymbNumUnaryElementaryFn a
  SymbRecip :: Fractional a => SymbNumUnaryElementaryFn a
  SymbElementaryFloating
     :: Floating a => SymbElementaryFlFn a -> SymbNumUnaryElementaryFn a

deriving instance Eq (SymbNumUnaryElementaryFn a)
deriving instance Show (SymbNumUnaryElementaryFn a)


data SymbElementaryFlFn :: Type -> Type where
  SymbExp, SymbLog, SymbSqrt, SymbSin, SymbCos, SymbTan, SymbAsin, SymbAcos
   , SymbAtan, SymbSinh, SymbCosh, SymbTanh, SymbAsinh, SymbAcosh, SymbAtanh
      :: SymbElementaryFlFn a

deriving instance Eq (SymbElementaryFlFn a)
deriving instance Show (SymbElementaryFlFn a)

data SymbNumBinaryElementaryFn a where
  SymbAdd, SymbSubtract :: AdditiveGroup a => SymbNumBinaryElementaryFn a
  SymbPow :: Floating a => SymbNumBinaryElementaryFn a
  SymbLogBase :: Floating a => SymbNumBinaryElementaryFn a
  SymbMul :: Num a => SymbNumBinaryElementaryFn a
  SymbDiv :: Fractional a => SymbNumBinaryElementaryFn a

deriving instance Eq (SymbNumBinaryElementaryFn a)
deriving instance Show (SymbNumBinaryElementaryFn a)


instance Category (SymbNumFn ζ) where
  id = SymbId
  SymbId . g = g
  f . SymbId = f
  SymbConst c . _ = SymbConst c
  f . SymbCompo g γ = SymbCompo (f . g) γ -- Store composition in left-associative
                                          -- form, to aid common-subexpression
                                          -- elimination in &&&.
  f . g = SymbCompo f g

instance ζ () => Cartesian (SymbNumFn ζ) where
  swap = SymbSwap
  attachUnit = id &&& terminal
  detachUnit = fst
  regroup = SymbRegroup
  regroup' = SymbRegroup'

instance ζ () => Morphism (SymbNumFn ζ) where
  f***g = SymbPar f g

infix 4 ===
(===) :: ∀ a b . (Eq a, Typeable a, Typeable b)
   => a -> b -> Maybe (a:~:b)
x===y = case eqT @a @b of
  Just Refl | x==y  -> Just Refl
  _ -> Nothing

instance ζ () => PreArrow (SymbNumFn ζ) where
  SymbId &&& SymbId = SymbCopy
  SymbConst x &&& SymbConst y
   | Just Refl <- x===y
       = SymbCompo SymbCopy (SymbConst x)
  SymbUnaryElementary f &&& SymbUnaryElementary g
   | f==g    = SymbCompo SymbCopy (SymbUnaryElementary f)
  SymbBinaryElementary f &&& SymbBinaryElementary g
   | f==g    = SymbCompo SymbCopy (SymbBinaryElementary f)
  f &&& SymbCompo g γ
   | SymbCompo SymbCopy h <- f&&&γ
       = (id&&&g) . h
  SymbCompo f φ &&& g
   | SymbCompo SymbCopy h <- φ&&&g
       = (f&&&id) . h
  SymbCompo f φ &&& SymbCompo g γ = case φ&&&γ of
    SymbCopy -> f&&&g
    SymbCompo SymbCopy h -> (f&&&g) . h
    φγ -> (f***g) . φγ
  SymbPar f φ &&& SymbPar g γ
   | (SymbCompo SymbCopy fg, SymbCompo SymbCopy φγ) <- (f&&&g, φ&&&γ)
       = SymbCompo SymbCopy (SymbPar fg φγ)
  SymbCopy &&& SymbCopy = SymbCompo SymbCopy SymbCopy
  SymbSwap &&& SymbSwap = SymbCompo SymbCopy SymbSwap
  SymbRegroup &&& SymbRegroup = SymbCompo SymbCopy SymbRegroup
  SymbRegroup' &&& SymbRegroup' = SymbCompo SymbCopy SymbRegroup'
  SymbFst &&& SymbFst = SymbCompo SymbCopy SymbFst
  SymbSnd &&& SymbSnd = SymbCompo SymbCopy SymbSnd
  SymbScalarMul &&& SymbScalarMul = SymbCompo SymbCopy SymbScalarMul
  SymbInnerProd &&& SymbInnerProd = SymbCompo SymbCopy SymbInnerProd
  SymbScalarDiv &&& SymbScalarDiv = SymbCompo SymbCopy SymbScalarDiv
  f&&&g = SymbCompo (SymbPar f g) SymbCopy

  terminal = SymbConst ()
  fst = SymbFst
  snd = SymbSnd

type CET ζ o = (ζ o, Eq o, Typeable o)

instance ζ () => WellPointed (SymbNumFn ζ) where
  type PointObject (SymbNumFn ζ) o = (CET ζ o)
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

instance (ζ (), CET ζ x) => PointAgent (SymbNumVal ζ) (SymbNumFn ζ) a x where
  point = genericPoint


instance (AdditiveGroup x, ζ (), CET ζ x) => AdditiveGroup (SymbNumVal ζ a x) where
  zeroV = point zeroV
  (^+^) = genericAgentCombine (SymbBinaryElementary SymbAdd)
  (^-^) = genericAgentCombine (SymbBinaryElementary SymbSubtract)
  negateV = genericAgentMap (SymbUnaryElementary SymbNegate)

instance (VectorSpace v, ζ (), CET ζ v) => VectorSpace (SymbNumVal ζ a v) where
  type Scalar (SymbNumVal ζ a v) = SymbNumVal ζ a (Scalar v)
  (*^) = flip $ genericAgentCombine SymbScalarMul

instance (VectorSpace n, Num n, n ~ Scalar n, ζ (), CET ζ n)
            => Num (SymbNumVal ζ a n) where
  fromInteger = point . fromInteger
  (+) = (^+^)
  (-) = (^-^)
  (*) = genericAgentCombine (SymbBinaryElementary SymbMul)
  negate = negateV
  abs = genericAgentMap (SymbUnaryElementary SymbAbs)
  signum = genericAgentMap (SymbUnaryElementary SymbSignum)

instance (VectorSpace n, Fractional n, n ~ Scalar n, ζ (), CET ζ n)
            => Fractional (SymbNumVal ζ a n) where
  fromRational = point . fromRational
  recip = genericAgentMap (SymbUnaryElementary SymbRecip)
  (/) = genericAgentCombine (SymbBinaryElementary SymbDiv)

floatingAgentMap :: (VectorSpace n, Floating n, n ~ Scalar n, ζ (), CET ζ n)
     => SymbElementaryFlFn n -> SymbNumVal ζ a n -> SymbNumVal ζ a n
floatingAgentMap = genericAgentMap . SymbUnaryElementary . SymbElementaryFloating

instance (VectorSpace n, Floating n, n ~ Scalar n, ζ (), CET ζ n)
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

  arr SymbScalarMul (v,μ) = μ*^v
  arr SymbScalarDiv (v,μ) = v^/μ
  arr SymbInnerProd (v,w) = v<.>w

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
     SymbMul -> x*y
     SymbDiv -> x/y
     SymbSubtract -> x^-^y
     SymbLogBase -> logBase x y
     SymbPow -> x**y

