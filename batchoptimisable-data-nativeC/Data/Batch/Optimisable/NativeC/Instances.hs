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

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe as DBO (unsafeIO)
import Data.Batch.Optimisable.NativeC.Internal

import Data.AffineSpace
import Data.AdditiveGroup
import Data.VectorSpace
import Data.Basis
import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Category

import qualified Data.Vector as VB
import qualified Data.Vector.Unboxed as VU

import Control.Monad
import Control.Lens.Indexed (TraversableWithIndex(..))
import Control.Monad.Trans.State
import Control.Monad.Trans.Class (lift)
import Control.Arrow (first)
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Foldable as Fldb

import GHC.TypeLits (KnownNat)
import GHC.Exts (IsList(..))
import Data.Kind (Type)
import Data.Type.Coercion

import qualified Test.QuickCheck as QC

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

newtype MABasis dims = MABasis Int
 deriving (Eq)
instance ∀ dims . (KnownShape dims) => IsList (MABasis dims) where
  type Item (MABasis dims) = Int
  fromList l
    | length l == length shp
         = MABasis . sum $ zipWith (*) (tail $ scanr (*) 1 shp) l
   where shp = shape @dims
  toList (MABasis il) = snd $ go (shape @dims)
   where go [] = (il,[])
         go (ld:lds) = case go lds of
           (il',ixs) -> case il'`divMod`ld of
                (il'', ix) -> (il'', ix:ixs)
instance KnownShape dims => Show (MABasis dims) where
    show = show . toList

instance ∀ dims . KnownShape dims => QC.Arbitrary (MABasis dims) where
  arbitrary = MABasis <$> QC.choose (0, product $ shape @dims)
  shrink (MABasis i) = MABasis <$> QC.shrink i

instance (HasBasis t, VU.Unbox t, KnownShape dims, Num (Scalar t))
              => HasBasis (MultiArray dims t) where
  type Basis (MultiArray dims t) = (MABasis dims, Basis t)
  decompose (MultiArray a)
       = [ ((MABasis i, bt), tj)
         | i <- allIndices @dims
         , let t = VU.unsafeIndex a i
         , (bt, tj) <- decompose t ]
  decompose' (MultiArray a) (MABasis i, j) = decompose' (VU.unsafeIndex a i) j
  basisValue (MABasis i, j) = placeAtIndex i $ basisValue j

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

l2t :: (v+>w) -> (DualVector v⊗w)
l2t (LinearMap f) = Tensor f

l'2t :: ∀ v w . LinearSpace v => (DualVector v+>w) -> (v⊗w)
l'2t = case dualSpaceWitness @v of
  DualSpaceWitness -> \(LinearMap f) -> Tensor f

t2l :: (DualVector v⊗w) -> (v+>w)
t2l (Tensor f) = LinearMap f

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

instance ∀ dims . KnownShape dims
            => FiniteDimensional (MultiArray dims Double) where
  data SubBasis (MultiArray dims Double) = MASB
  entireBasis = MASB
  enumerateSubBasis MASB
             = [ placeAtIndex i 1
               | i <- allIndices @dims ]
  subbasisDimension MASB = product (shape @dims)
  decomposeLinMap (LinearMap l) = (MASB, ((getTensorProduct<$>l)++))
  decomposeLinMapWithin MASB (LinearMap l)
      = Right ((getTensorProduct<$>l)++)
  recomposeSB MASB l = case splitAt n l of
     (lR, r) | length lR == n
            -> (MultiArray $ VU.fromList lR, r)
   where n = product $ shape @dims
  recomposeSBTensor MASB sbw l = first Tensor $ go n l
   where go nr l
           | nr<1       = ([], l)
           | otherwise  = case recomposeSB sbw l of
               (w, dc') -> first (Tensor w:) $ go (nr-1) dc'
         n = product $ shape @dims
  recomposeLinMap MASB l = case splitAt n l of
     (lR, r) | length lR == n
            -> (LinearMap $ Tensor<$>lR, r)
   where n = product $ shape @dims
  recomposeContraLinMap fw mv
           = LinearMap [ Tensor . fw $
                          fmap (\(MultiArray a)->VU.unsafeIndex a i) mv
                       | i <- allIndices @dims ]
  uncanonicallyFromDual = LinearFunction id
  uncanonicallyToDual = LinearFunction id

instance ∀ dims . KnownShape dims
            => TensorDecomposable (MultiArray dims Double) where
  tensorDecomposition (Tensor t)
      = [ ((MABasis i, ()), w)
        | (i, Tensor w) <- zip [0..] t ]
  showsPrecBasis = showsPrec
instance ∀ dims . KnownShape dims
            => RieszDecomposable (MultiArray dims Double) where
  rieszDecomposition f
      = [ ((MABasis i, ()), uncanonicallyFromDual-+$>fromFlatTensor
                           -+$> (fmapTensor-+$>LinearFunction
                                  `id` \(MultiArray a) -> VU.unsafeIndex a i)
                             -+$>l2t f)
        | i <- allIndices @dims ]



instance ∀ dims s t w . (KnownShape dims, QC.Arbitrary (t⊗w), s ~ Scalar t)
    => QC.Arbitrary (Tensor s (MultiArray dims t) w) where
  arbitrary = Tensor <$> replicateM (product $ shape @dims) QC.arbitrary
  shrink (Tensor a) = case a of
       [] -> []
       l  -> Tensor . NE.toList <$>
                          NE.tail (transposeRep . NE.fromList
                                    $ zipWith (:|) l (QC.shrink<$>l))
instance ∀ dims s t w . ( KnownShape dims, QC.Arbitrary (t+>w)
                        , LinearSpace t, Scalar t~s )
    => QC.Arbitrary (LinearMap s (MultiArray dims t) w) where
  arbitrary = case dualSpaceWitness @t of
    DualSpaceWitness -> LinearMap <$> replicateM (product $ shape @dims)
                                                 (l'2t <$> QC.arbitrary)
  shrink (LinearMap a) = case dualSpaceWitness @t of
    DualSpaceWitness -> case t2l<$>a of
       [] -> []
       l  -> LinearMap . map l'2t . NE.toList <$>
                          NE.tail (transposeRep . NE.fromList
                                    $ zipWith (:|) l (QC.shrink<$>l))
instance ∀ dims t r s
    . ( KnownShape dims, VU.Unbox t, InnerSpace (t⊗r)
      , TensorSpace r, Num s
      , TensorSpace t, Needle t ~ t, VU.Unbox s
      , Scalar t~s, Scalar r~s )
              => InnerSpace (Tensor s (MultiArray dims t) r) where
  Tensor f <.> Tensor g = sum $ zipWith (<.>) f g
instance ∀ dims t r s
    . ( KnownShape dims, VU.Unbox t, InnerSpace (t+>r)
      , TensorSpace r
      , LinearSpace t, Needle t ~ t, VU.Unbox s, VU.Unbox (DualVector t)
      , Scalar t~s, Scalar r~s )
              => InnerSpace (LinearMap s (MultiArray dims t) r) where
  LinearMap f <.> LinearMap g = sum $ zipWith (<.>) (t2l<$>f :: [t+>r]) (t2l<$>g)

instance ∀ dims t r s
    . ( KnownShape dims, VU.Unbox t, Eq (t⊗r), Scalar t~s, Scalar r~s )
              => Eq (Tensor s (MultiArray dims t) r) where
  Tensor f == Tensor g = f==g
instance ∀ dims t r s
    . ( KnownShape dims, VU.Unbox t, Eq (t+>r), Scalar t~s, Scalar r~s )
              => Eq (LinearMap s (MultiArray dims t) r) where
  LinearMap f == LinearMap g = (t2l<$>f :: [t+>r])==(t2l<$>g)

instance ( KnownShape dims, Show (MultiArray dims Double)
         , TensorDecomposable v, Scalar v ~ Double, Show v)
              => Show (Tensor Double v (MultiArray dims Double)) where
  showsPrec = tensorDecomposeShowsPrec
instance ( KnownShape dims
         , FiniteDimensional v, v ~ DualVector v, Scalar v ~ Double, Show v)
              => Show (LinearMap Double v (MultiArray dims Double)) where
  showsPrec = rieszDecomposeShowsPrec

compressLinMap :: ∀ d e t . ( KnownShape d, KnownShape e, VU.Unbox t
                            , TensorProduct (DualVector t) (MultiArray e t)
                                ~ MultiArray e t )
      => LinearMap (Scalar t) (MultiArray d t) (MultiArray e t)
           -> MultiArray (d++e) t
compressLinMap (LinearMap f) = MultiArray . VU.concat
          $ getFlatArray . getTensorProduct<$>f

uncompressLinMap :: ∀ d e t . ( KnownShape d, KnownShape e, VU.Unbox t
                            , TensorProduct (DualVector t) (MultiArray e t)
                                ~ MultiArray e t )
    => MultiArray (d++e) t
      -> LinearMap (Scalar t) (MultiArray d t) (MultiArray e t)
uncompressLinMap (MultiArray a)
   = LinearMap [ Tensor . MultiArray
                   $ VU.unsafeSlice (i*ne) ne a
               | i <- allIndices @d ]
 where ne = product $ shape @e


instance ∀ d e t s
         . ( KnownShape d, KnownShape e
           , CPortable t, Scalar t ~ s
           , TensorProduct (DualVector t) (MultiArray e t)
                                ~ MultiArray e t )
    => BatchOptimisable (LinearMap s (MultiArray d t)
                                     (MultiArray e t)) where
  data Optimised (LinearMap s (MultiArray d t)
                              (MultiArray e t)) σ τ
        = OptdArrLinMap { getOptLinMapASArr
              :: Optimised (MultiArray (d++e) t) σ τ }
  allocateBatch = case tensorShapeKnowledge @d @e of
    ShapeKnowledge -> \batch
      -> OptdArrLinMap <$> allocateBatch (compressLinMap <$> batch)
  peekSingleSample = case tensorShapeKnowledge @d @e of
    ShapeKnowledge -> \(OptdArrLinMap p) j
      -> fmap uncompressLinMap <$> peekSingleSample p j
  peekOptimised = case tensorShapeKnowledge @d @e of
    ShapeKnowledge -> \(OptdArrLinMap p)
         -> fmap uncompressLinMap <$> peekOptimised p

instance ∀ d w t s
         . ( KnownShape d
           , CPortable t
           , TensorSpace w, BatchOptimisable w, Scalar w ~ t
           , Num' t, Scalar t ~ s
           , TensorProduct (DualVector t) w ~ w )
    => BatchOptimisable (LinearFunction s (MultiArray d t) w) where
  data Optimised (LinearFunction s (MultiArray d t) w) σ τ
        = OptdArrLinFunc {
             olfShape :: τ ()
           , runOptdLinFunc
                :: Optimised (MultiArray d t) σ τ
                  -> OptimiseM σ (Optimised w σ τ) }
  allocateBatch batch = pure . OptdArrLinFunc (const()<$>batch)
           $ \a -> do
       inputs <- peekOptimised a
       outputs <- (`evalStateT`Fldb.toList batch) . forM inputs $ \x -> do
             (f:fs) <- get
             put fs
             return $ f -+$> x
       allocateBatch outputs
  peekSingleSample = case ( linearManifoldWitness @t
                       , closedScalarWitness @t
                       , trivialTensorWitness @t ) of
   (LinearManifoldWitness, ClosedScalarWitness, TrivialTensorWitness)
            -> \(OptdArrLinFunc shp fs) j -> do
     outputBatches <- forM (allIndices @d) $ \i -> do
        let inputArr = placeAtIndex i 1
        inputBatch <- allocateBatch $ const inputArr <$> shp
        fs inputBatch  -- This is really inefficient: we're running the function
                       -- for a whole batch, but only extract a single result.
                       -- Not sure if there's a better alternative.
     relevantResults <- forM outputBatches $ \batchR -> do
       Just batchR' <- peekSingleSample batchR j
       return $ Tensor batchR'
     return . Just $ applyLinear-+$>LinearMap relevantResults
  peekOptimised = case ( linearManifoldWitness @t
                       , closedScalarWitness @t
                       , trivialTensorWitness @t ) of
   (LinearManifoldWitness, ClosedScalarWitness, TrivialTensorWitness)
            -> \(OptdArrLinFunc shp fs) -> do
     outputBatches <- forM (allIndices @d) $ \i -> do
        let inputArr = placeAtIndex i 1
        inputBatch <- allocateBatch $ const inputArr <$> shp
        outputBatch <- fs inputBatch
        Fldb.toList <$> peekOptimised outputBatch
     (`evalStateT`outputBatches) . (`traverse`shp) $ \() -> do
          relevantResults <- map (Tensor . head)<$>get
          modify $ map tail
          return $ applyLinear-+$>LinearMap relevantResults
