-- |
-- Module      : Data.Batch.Optimisable.NativeC.Instances.SymbNumFmapping
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
{-# LANGUAGE CPP                    #-}


module Data.Batch.Optimisable.NativeC.Instances.SymbNumFmapping where

import Data.Batch.Optimisable
import Data.Batch.Optimisable.Unsafe
import Data.Batch.Optimisable.NativeC.Internal

import Math.Category.SymbolicNumFunction

#ifdef DEBUG_SYMBNUMFN_FMAPPING
import GHC.Stack (HasCallStack)
#endif

numFmapArrayGenericBatchOptimised_cps :: ∀ a b dims s τ φ
      . ( OptimisedNumArg a
#ifdef DEBUG_SYMBNUMFN_FMAPPING
        , HasCallStack
#endif
        , KnownShape dims, Traversable τ )
    => SymbNumFn OptimisedNumArg a b
        -> (OptimisedNumArg b =>
              (Optimised (OptResArray a dims) s τ
                 -> OptimiseM s (Optimised (OptResArray b dims) s τ))
             -> φ ) -> φ
numFmapArrayGenericBatchOptimised_cps SymbId q = q pure
numFmapArrayGenericBatchOptimised_cps (SymbConst c) q = q (\i -> do
  shp <- peekOptNumArgShape i
  optimiseConstNumArg c shp
 )
numFmapArrayGenericBatchOptimised_cps (SymbCompo f g) q
   = numFmapArrayBatchOptimised_compo_cps f g q
#ifdef DEBUG_SYMBNUMFN_FMAPPING
numFmapArrayGenericBatchOptimised_cps f _ = error
    $ "Cannot handle " ++ show f
#endif



data UnitOptResArray dims = UnitOptResArray


type instance OptResArray () dims = UnitOptResArray dims
instance OptimisedNumArg () where
  numFmapArrayBatchOptimised_cps = numFmapArrayGenericBatchOptimised_cps



numFmapArrayScalarBatchOptimised_cps :: ∀ a b dims s τ φ
      . ( OptimisedNumArg a
        , OptResArray a dims ~ MultiArray dims a
        , CPortable a, Real a
        , Fractional (CCType a), CNum (CCType a)
        , BatchOptimisable (OptResArray a dims)
        , KnownShape dims, Traversable τ
#ifdef DEBUG_SYMBNUMFN_FMAPPING
        , HasCallStack
#endif
        )
    => SymbNumFn OptimisedNumArg a b
        -> (OptimisedNumArg b =>
              (Optimised (OptResArray a dims) s τ
                 -> OptimiseM s (Optimised (OptResArray b dims) s τ))
             -> φ ) -> φ
numFmapArrayScalarBatchOptimised_cps SymbId q = q pure
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
#ifdef DEBUG_SYMBNUMFN_FMAPPING
numFmapArrayScalarBatchOptimised_cps f _ = error
    $ "Cannot handle " ++ show f
#endif

type instance OptResArray Double dims = MultiArray dims Double
instance OptimisedNumArg Double where
  numFmapArrayBatchOptimised_cps = numFmapArrayScalarBatchOptimised_cps
  numFmapArrayBatchTupleOptimised_cps = numFmapArrayBatchScalarTupleOptimised_cps

numFmapArrayTupleBatchOptimised_cps :: ∀ a dims τ b c s φ
    . ( OptimisedNumArg a
#ifdef DEBUG_SYMBNUMFN_FMAPPING
      , HasCallStack
#endif
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg a (b,c)
      -> ( (OptimisedNumArg b, OptimisedNumArg c)
             => (Optimised (OptResArray a dims) s τ
            -> OptimiseM s (Optimised (OptResArray b dims, OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayTupleBatchOptimised_cps f q = case numFmapArrayBatchOptimised_cps f of
    rf -> rf (\q'f -> useIndividualTupNumOpts @(b,c) @b @c q q'f)

numFmapArrayBatchOptimised_compo_cps :: ∀ a b c dims τ s φ
    . ( OptimisedNumArg a
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg b c -> SymbNumFn OptimisedNumArg a b
      -> ( OptimisedNumArg c
             => (Optimised (OptResArray a dims) s τ
            -> OptimiseM s (Optimised (OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayBatchOptimised_compo_cps f g q
  = let rg :: (OptimisedNumArg b => (Optimised (OptResArray a dims) s τ
                           -> OptimiseM s (Optimised (OptResArray b dims) s τ))
                    -> φ ) -> φ
        rg = numFmapArrayBatchOptimised_cps g
    in rg (\q'g ->
     let rf :: (OptimisedNumArg c => (Optimised (OptResArray b dims) s τ
                                  -> OptimiseM s (Optimised (OptResArray c dims) s τ))
                    -> φ ) -> φ
         rf = numFmapArrayBatchOptimised_cps f
     in rf (\q'f -> q (\x -> do
            gvx <- q'g x
            q'f gvx
          )))

numFmapArrayTupleBatchOptimised_par_cps :: ∀ x y dims τ b c s φ
    . ( OptimisedNumArg (x,y)
#ifdef DEBUG_SYMBNUMFN_FMAPPING
      , HasCallStack
#endif
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg x b -> SymbNumFn OptimisedNumArg y c
      -> ( (OptimisedNumArg b, OptimisedNumArg c)
             => (Optimised (OptResArray (x,y) dims) s τ
            -> OptimiseM s (Optimised (OptResArray b dims, OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayTupleBatchOptimised_par_cps f g q
  = useIndividualTupNumOpts @(x,y) @x @y
     (let rf :: (OptimisedNumArg b => (Optimised (OptResArray x dims) s τ
                                  -> OptimiseM s (Optimised (OptResArray b dims) s τ))
                    -> φ ) -> φ
          rf = numFmapArrayBatchOptimised_cps f
          rg :: (OptimisedNumArg c => (Optimised (OptResArray y dims) s τ
                                  -> OptimiseM s (Optimised (OptResArray c dims) s τ))
                    -> φ ) -> φ
          rg = numFmapArrayBatchOptimised_cps g
      in rf (\q'f -> rg (\q'g -> q (\(OptimisedTuple x y) -> do
            fhvx <- q'f x
            ghvy <- q'g y
            return $ OptimisedTuple fhvx ghvy
          ))))


numFmapArrayBatchScalarTupleOptimised_cps :: ∀ a dims τ b c s φ
    . ( OptimisedNumArg a, OptimisedNumArg b
      , OptResArray a dims ~ MultiArray dims a
      , CPortable a, Real a
      , Fractional (CCType a), CNum (CCType a)
      , BatchOptimisable (OptResArray a dims)
#ifdef DEBUG_SYMBNUMFN_FMAPPING
      , HasCallStack
#endif
      , KnownShape dims, Traversable τ )
  => SymbNumFn OptimisedNumArg (a,b) c
      -> ( OptimisedNumArg c
             => (Optimised (OptResArray a dims, OptResArray b dims) s τ
            -> OptimiseM s (Optimised (OptResArray c dims) s τ)
             ) -> φ
         ) -> φ
numFmapArrayBatchScalarTupleOptimised_cps (SymbPar f g) q
   = numFmapArrayTupleBatchOptimised_par_cps f g q

type instance OptResArray (b,c) dims = (OptResArray b dims, OptResArray c dims)
instance (OptimisedNumArg b, OptimisedNumArg c)
      => OptimisedNumArg (b,c) where
  numFmapArrayBatchOptimised_cps = numFmapArrayBatchTupleOptimised_cps
