-- |
-- Module      : Data.Batch.Optimisable.NativeC.Internal
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE QuasiQuotes            #-}
{-# LANGUAGE TemplateHaskell        #-}


module Data.Batch.Optimisable.NativeC.Internal where

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe

import Data.Kind(Type)
import Data.Traversable
import qualified Data.Foldable as Foldable
import GHC.TypeLits
import GHC.Exts (IsList(..))
import Data.Proxy
import Data.Semigroup ((<>))

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VSM

import Control.Monad
import Control.Arrow (first)

import qualified Test.QuickCheck as QC

import System.IO.Unsafe
import Control.Monad.Primitive (PrimMonad, PrimState)
import Data.IORef
import qualified Language.C.Inline as C
import Data.Int
import Foreign.C.Types (CInt, CLong, CFloat, CDouble)
import Foreign (Ptr)

import Math.Category.SymbolicNumFunction


type family (++) (l :: [k]) (m :: [k]) :: [k] where
  '[] ++ m = m
  (h ': t) ++ m = h ': (t++m)

class KnownShape (dims :: [Nat]) where
  shape :: [Int]
  tensorShapeKnowledge' :: KnownShape e
      => Proxy e -> ShapeKnowledge (dims++e)

tensorShapeKnowledge :: ∀ d e . (KnownShape d, KnownShape e)
                            => ShapeKnowledge (d++e)
tensorShapeKnowledge = tensorShapeKnowledge' @d @e Proxy

instance KnownShape '[] where
  shape = []
  tensorShapeKnowledge' _ = ShapeKnowledge
instance ∀ n ns . (KnownNat n, KnownShape ns) => KnownShape (n ': ns) where
  shape = nv @n : shape @ns
  tensorShapeKnowledge' p = case tensorShapeKnowledge' @ns p of
          ShapeKnowledge -> ShapeKnowledge

data ShapeKnowledge (l :: [Nat]) where
  ShapeKnowledge :: KnownShape l => ShapeKnowledge l


newtype MultiArray (dims :: [Nat]) t
  = MultiArray { getFlatArray :: VU.Vector t }
 deriving (Eq, Ord)

constArray :: ∀ a dims . (VU.Unbox a, KnownShape dims)
          => a -> MultiArray dims a
constArray = MultiArray . VU.replicate (product $ shape @dims)

mapArray :: (VU.Unbox a, VU.Unbox b)
          => (a -> b) -> MultiArray dims a -> MultiArray dims b
mapArray f (MultiArray v) = MultiArray $ VU.map f v

zipArrayWith :: (VU.Unbox a, VU.Unbox b, VU.Unbox c)
          => (a -> b -> c)
            -> MultiArray dims a -> MultiArray dims b -> MultiArray dims c
zipArrayWith f (MultiArray v) (MultiArray w) = MultiArray $ VU.zipWith f v w

mapMArray :: (VU.Unbox a, VU.Unbox b, Monad f)
          => (a -> f b) -> MultiArray dims a -> f (MultiArray dims b)
mapMArray f (MultiArray v) = MultiArray <$> VU.mapM f v

nv :: ∀ n i . (KnownNat n, Integral i) => i
nv = fromInteger $ natVal (Proxy @n)

instance ∀ n ns t . (KnownNat n, KnownShape ns, VU.Unbox t)
        => IsList (MultiArray (n ': ns) t) where
  type Item (MultiArray (n ': ns) t) = MultiArray ns t
  toList (MultiArray a) = [ MultiArray $ VU.slice (i*nBloc) nBloc a
                          | i <- [0..n₀-1] ]
   where n₀ = nv @n
         nBloc = product $ shape @ns
  fromList l
    | length l == n₀  = MultiArray . VU.concat $ getFlatArray<$>l
   where n₀ = nv @n


instance (Show t, VU.Unbox t) => Show (MultiArray '[] t) where
  showsPrec p (MultiArray a) = showsPrec p $ a VU.! 0
instance ∀ n ns t . ( KnownNat n, KnownShape ns, VU.Unbox t
                    , Show t, Show (MultiArray ns t) )
                   => Show (MultiArray (n ': ns) t) where
  show = show . GHC.Exts.toList

instance (Num t, VU.Unbox t) => Num (MultiArray '[] t) where
  fromInteger = constArray . fromInteger
  abs = mapArray abs
  signum = mapArray signum
  negate = mapArray negate
  (+) = zipArrayWith (+)
  (*) = zipArrayWith (*)

transposeRep :: NonEmpty (NonEmpty a) -> NonEmpty (NonEmpty a)
transposeRep l = (NE.head <$> l)
     :| if Foldable.all (null . NE.tail) l
         then []
         else NE.toList . transposeRep $ fmap shTail l
 where shTail (h:|[]) = h:|[]
       shTail (_:|h:t) = h:|t


instance ∀ dims t . (KnownShape dims, VU.Unbox t, QC.Arbitrary t)
            => QC.Arbitrary (MultiArray dims t) where
  arbitrary = MultiArray <$> VU.replicateM (product $ shape @dims)
                                           QC.arbitrary
  shrink (MultiArray a) = case VU.toList a of
       [] -> []
       l  -> MultiArray . VU.fromList . NE.toList <$>
                          NE.tail (transposeRep . NE.fromList
                                    $ zipWith (:|) l (QC.shrink<$>l))


type CIntArray n = MultiArray '[n] Int32
type CLongArray n = MultiArray '[n] Int
type CFloatArray n = MultiArray '[n] Float
type CDoubleArray n = MultiArray '[n] Double

C.context (C.baseCtx <> C.vecCtx)
C.include "<stdlib.h>"
C.include "<string.h>"
C.include "<math.h>"

class VS.Storable c => CHandleable c where
  callocArray :: CInt -> IO (Ptr c)
  releaseArray :: Ptr c -> IO ()
  makeArrayConst :: Ptr c -- ^ Array to modify
             -> CInt      -- ^ Number of elements to update
             -> c         -- ^ Value that each value in array should take
             -> IO ()
  memcpyArray :: (Ptr c, CInt) -- ^ Target, with offset
              -> (Ptr c, CInt) -- ^ Source, with offset
              -> CInt          -- ^ Number of elements
              -> IO ()

class (VU.Unbox t, CHandleable (CCType t)) => CPortable t where
  type CCType t :: Type
  thawForC :: PrimMonad m
    => VU.Vector t -> m (VSM.MVector (PrimState m) (CCType t))
  freezeFromC :: PrimMonad m
    => VSM.MVector (PrimState m) (CCType t) -> m (VU.Vector t)
  mapPrimitiveNumFunctionToArray
              :: SymbNumFn ζ t t        -- ^ Function to map
              -> (Ptr (CCType t), CInt) -- ^ Target, with offset
              -> (Ptr (CCType t), CInt) -- ^ Source, with offset
              -> CInt                   -- ^ Number of elements
              -> IO ()

class CHandleable n => CNum n where
  addArrays ::   (Ptr n, CInt) -- ^ Target, with offset
              -> (Ptr n, CInt) -- ^ First source, with offset
              -> (Ptr n, CInt) -- ^ Second source, with offset
              -> CInt          -- ^ Number of elements
              -> IO ()

instance CHandleable CInt where
  callocArray nElems = [C.exp| int* {calloc($(int nElems), sizeof(int))} |]
  releaseArray loc = [C.block| void { free ($(int* loc)); } |]
  makeArrayConst loc nElems c
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(int* loc)[i] = $(int c);
                     } } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(int* tgt) + $(int tOffs)
                             , $(int* src) + $(int sOffs)
                             , $(int nElems) * sizeof(int)
                             ); } |]
instance CPortable Int32 where
  type CCType Int32 = CInt -- may be invalid on non-LinuxAMD64
  thawForC = VS.thaw . VS.map fromIntegral . VU.convert
  freezeFromC = fmap (VU.convert . VS.map fromIntegral) . VS.freeze

instance CHandleable CLong where
  callocArray nElems = [C.exp| long* {calloc($(int nElems), sizeof(long))} |]
  releaseArray loc = [C.block| void { free ($(long* loc)); } |]
  makeArrayConst loc nElems c
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(long* loc)[i] = $(long c);
                     } } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(long* tgt) + $(int tOffs)
                             , $(long* src) + $(int sOffs)
                             , $(int nElems) * sizeof(long)
                             ); } |]
instance CPortable Int where
  type CCType Int = CLong -- may be invalid on non-LinuxAMD64
  thawForC = VS.thaw . VS.map fromIntegral . VU.convert
  freezeFromC = fmap (VU.convert . VS.map fromIntegral) . VS.freeze

instance CHandleable CFloat where
  callocArray nElems = [C.exp| float* {calloc($(int nElems), sizeof(float))} |]
  releaseArray loc = [C.block| void { free ($(float* loc)); } |]
  makeArrayConst loc nElems c
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(float* loc)[i] = $(float c);
                     } } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(float* tgt) + $(int tOffs)
                             , $(float* src) + $(int sOffs)
                             , $(int nElems) * sizeof(float)
                             ); } |]
instance CPortable Float where
  type CCType Float = CFloat
  thawForC = VS.thaw . VS.map realToFrac . VU.convert
  freezeFromC = fmap (VU.convert . VS.map realToFrac) . VS.freeze

instance CHandleable CDouble where
  callocArray nElems = [C.exp| double* {calloc($(int nElems), sizeof(double))} |]
  releaseArray loc = [C.block| void { free ($(double* loc)); } |]
  makeArrayConst loc nElems c
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(double* loc)[i] = $(double c);
                     } } |]
  memcpyArray (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { memcpy( $(double* tgt) + $(int tOffs)
                             , $(double* src) + $(int sOffs)
                             , $(int nElems) * sizeof(double)
                             ); } |]
instance CNum CDouble where
  addArrays (tgt, tOffs) (src0, s0Offs) (src1, s1Offs) nElems
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(double* tgt)[$(int tOffs) + i]
                             = $(double* src0)[$(int s0Offs) + i]
                             + $(double* src1)[$(int s1Offs) + i];
                     } } |]
instance CPortable Double where
  type CCType Double = CDouble
  thawForC = VS.thaw . VS.map realToFrac . VU.convert
  freezeFromC = fmap (VU.convert . VS.map realToFrac) . VS.freeze
  mapPrimitiveNumFunctionToArray (SymbUnaryElementary SymbAbs)
                             (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         $(double* tgt)[$(int tOffs)+i]
                             = fabs($(double* src)[$(int sOffs)+i]);
                     } } |]
  mapPrimitiveNumFunctionToArray (SymbUnaryElementary SymbRelu) (tgt, tOffs) (src, sOffs) nElems
    = [C.block| void { for (int i=0; i < $(int nElems); ++i) {
                         double r = $(double* src)[$(int sOffs)+i];
                         $(double* tgt)[$(int tOffs)+i]
                             = r<0? 0 : r;
                     } } |]

mapPrimitiveNumFunctionOnArray :: CPortable t
    => SymbNumFn ζ t t -> Ptr (CCType t) -> CInt -> IO (Ptr (CCType t))
mapPrimitiveNumFunctionOnArray f src nElems = do
   tgt <- callocArray nElems
   mapPrimitiveNumFunctionToArray f (tgt,0) (src,0) nElems
   return tgt

instance ∀ dims t . (KnownShape dims, CPortable t)
              => BatchOptimisable (MultiArray dims t) where
  data Optimised (MultiArray dims t) s τ
            = OptdArr { oiaShape :: τ ()
                      , oiaLocation :: Ptr (CCType t) }
  allocateBatch input = OptimiseM $ \_ -> do
    let nArr = fromIntegral . product $ shape @dims
        nBatch = Foldable.length input
        nElems = nArr * fromIntegral nBatch
    loc <- callocArray nElems
    iSt <- newIORef 0
    shp <- (`traverse`input) $ \(MultiArray a) -> do
      i <- readIORef iSt
      -- doing two copies, but efficiency is not a concern here...
      aC <- thawForC a
      VSM.unsafeWith aC $ \aCP -> memcpyArray (loc, nArr*i) (aCP, 0) nArr
      modifyIORef iSt (+1)
      return ()
    return ( OptdArr shp loc
           , pure $ RscReleaseHook (releaseArray loc) )
  peekBatchShape (OptdArr shp _) = pure shp
  peekOptimised (OptdArr shp loc) = OptimiseM $ \_ -> do
    let nArr = fromIntegral . product $ shape @dims
    tgt <- VSM.unsafeNew $ fromIntegral nArr
    iSt <- newIORef 0
    peekd <- forM shp $ \() -> do
      i <- readIORef iSt
      modifyIORef iSt (+1)
      VSM.unsafeWith tgt $ \tgtP
            -> memcpyArray (tgtP, 0) (loc, nArr*i) nArr
      MultiArray <$> freezeFromC tgt
    return (peekd, mempty)

primitiveNumFmapArrayBatchOptimised :: ∀ a dims s τ ζ
      . ( CPortable a, KnownShape dims, Foldable τ )
    => SymbNumFn ζ a a -> Optimised (MultiArray dims a) s τ
           -> OptimiseM s (Optimised (MultiArray dims a) s τ)
primitiveNumFmapArrayBatchOptimised f (OptdArr shp src) = OptimiseM $ \_ -> do
   let nArr = fromIntegral . product $ shape @dims
       nBatch = Foldable.length shp
       nElems = nArr * fromIntegral nBatch
   res <- mapPrimitiveNumFunctionOnArray f src nElems
   return ( OptdArr shp res
          , pure $ RscReleaseHook (releaseArray res) )

type family OptResArray r (dims :: [Nat]) = ora | ora -> r dims

class OptimisedNumArg a where
  peekOptNumArgShape :: Optimised (OptResArray a dims) s τ -> OptimiseM s (τ ())
  optimiseConstNumArg :: a -> τ () -> OptimiseM s (Optimised (OptResArray a dims) s τ)
  numFmapArrayBatchOptimised_cps :: ∀ r dims s τ φ
      . ( KnownShape dims, Traversable τ )
    => SymbNumFn OptimisedNumArg a r -> 
             ( OptimisedNumArg r => (Optimised (OptResArray a dims) s τ
                  -> OptimiseM s (Optimised (OptResArray r dims) s τ))
                 -> φ ) -> φ
  numFmapArrayBatchOptimised :: ∀ r dims s τ
      . ( KnownShape dims, Traversable τ )
    => SymbNumFn OptimisedNumArg a r -> Optimised (OptResArray a dims) s τ
           -> OptimiseM s (Optimised (OptResArray r dims) s τ)
  numFmapArrayBatchOptimised f x
      = numFmapArrayBatchOptimised_cps f (\q -> q x)
  useIndividualTupNumOpts :: ∀ x y φ . a ~ (x,y)
      => ( (OptimisedNumArg x, OptimisedNumArg y)
          => φ ) -> φ

numFmapArrayScalarBatchOptimised_cps :: ∀ a b dims s τ φ
      . ( OptimisedNumArg a
        , OptResArray a dims ~ MultiArray dims a
        , CPortable a, Real a
        , Fractional (CCType a), CNum (CCType a)
        , BatchOptimisable (OptResArray a dims)
        , KnownShape dims, Traversable τ )
    => SymbNumFn OptimisedNumArg a b
        -> (OptimisedNumArg b =>
              (Optimised (OptResArray a dims) s τ
                 -> OptimiseM s (Optimised (OptResArray b dims) s τ))
             -> φ ) -> φ
numFmapArrayScalarBatchOptimised_cps SymbId q = q pure
-- numFmapArrayScalarBatchOptimised (SymbConst c) i q = do
--   shp <- peekBatchShape i
--   optimiseConstNumArg c shp
--OptimiseM $ \_ -> do
-- let nArr = fromIntegral . product $ shape @dims
--     nBatch = Foldable.length shp
--     nElems = nArr * fromIntegral nBatch
-- loc <- callocArray nElems
-- makeArrayConst loc nElems $ realToFrac c
-- return ( OptdArr shp loc :: Optimised (OptResArray b dims) s τ
--        , pure $ RscReleaseHook (releaseArray loc) )
-- numFmapArrayScalarBatchOptimised (SymbCompo (SymbBinaryElementary f) g) x = do
--    shp <- peekOptNumArgShape x
--    OptimisedTuple (OptdArr _ vLoc) (OptdArr _ wLoc)
--        <- let dissect SymbCopy = numFmapArrayBatchOptimised SymbCopy x
--           in dissect g
--    OptimiseM $ \_ -> do
--       let nArr = fromIntegral . product $ shape @dims
--           nBatch = Foldable.length shp
--           nElems = nArr * fromIntegral nBatch
--       rLoc <- callocArray nElems
--       addArrays (rLoc,0) (vLoc,0) (wLoc,0) nElems
--       return ( OptdArr shp rLoc :: Optimised (OptResArray b dims) s τ
--              , pure $ RscReleaseHook (releaseArray rLoc) )

numFmapArrayScalarBatchOptimised_cps f@(SymbUnaryElementary _) q
    = q $ primitiveNumFmapArrayBatchOptimised f

type instance OptResArray Double dims = MultiArray dims Double
instance OptimisedNumArg Double where
  numFmapArrayBatchOptimised_cps = numFmapArrayScalarBatchOptimised_cps

numFmapArrayTupleBatchOptimised_cps :: ∀ a dims τ b c s φ
    . ( OptimisedNumArg a
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg a (b,c)
      -> ( (OptimisedNumArg b, OptimisedNumArg c)
             => (Optimised (OptResArray a dims) s τ
            -> OptimiseM s (Optimised (OptResArray b dims, OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayTupleBatchOptimised_cps SymbCopy q = q $ \v -> return $ OptimisedTuple v v
numFmapArrayTupleBatchOptimised_cps (SymbConst (β,γ)) q = undefined {- q $ \v -> do
   βv <- numFmapArrayBatchOptimised (SymbConst β) v
   γv <- numFmapArrayBatchOptimised (SymbConst γ) v
   return $ OptimisedTuple βv γv -}
numFmapArrayTupleBatchOptimised_cps (SymbPar f g) q
   = numFmapArrayTupleBatchOptimised_par_cps f g q
-- numFmapArrayTupleBatchOptimised_cps (SymbCompo (SymbPar f g) h) q
-- = case numFmapArrayTupleBatchOptimised_cps @a @dims @τ h of
--   rh -> rh (\q'h -> case ( numFmapArrayBatchOptimised_cps f
--                          , numFmapArrayBatchOptimised_cps g ) of
--     (rf, rg) -> _ {- rf (\q'f -> rg (\q'g -> q (\v -> do
--       OptimisedTuple hvx hvy <- q'h v
--       fhvx <- q'f hvx
--       ghvy <- q'g hvy
--       return $ OptimisedTuple fhvx ghvy
--      ))) -} )

numFmapArrayTupleBatchOptimised_par_cps :: ∀ x y dims τ b c s φ
    . ( OptimisedNumArg (x,y)
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg x b -> SymbNumFn OptimisedNumArg y c
      -> ( (OptimisedNumArg b, OptimisedNumArg c)
             => (Optimised (OptResArray (x,y) dims) s τ
            -> OptimiseM s (Optimised (OptResArray b dims, OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayTupleBatchOptimised_par_cps f g q
  = useIndividualTupNumOpts @(x,y) @x @y
     (case ( undefined -- numFmapArrayBatchOptimised_cps f
               :: (OptimisedNumArg b => (Optimised (OptResArray x dims) s τ
                                  -> OptimiseM s (Optimised (OptResArray b dims) s τ))
                    -> φ ) -> φ
           , undefined -- numFmapArrayBatchOptimised_cps g
               :: (OptimisedNumArg c => (Optimised (OptResArray y dims) s τ
                                  -> OptimiseM s (Optimised (OptResArray c dims) s τ))
                    -> φ ) -> φ
           ) of
        (rf, rg) -> rf undefined {- (\q'f -> rg (\q'g -> q (\(OptimisedTuple x y) -> do
            fhvx <- q'f x
            ghvy <- q'g y
            return $ OptimisedTuple fhvx ghvy
         ))) -} )
type instance OptResArray (b,c) dims = (OptResArray b dims, OptResArray c dims)
instance (OptimisedNumArg b, OptimisedNumArg c)
      => OptimisedNumArg (b,c) where
  numFmapArrayBatchOptimised_cps = undefined
