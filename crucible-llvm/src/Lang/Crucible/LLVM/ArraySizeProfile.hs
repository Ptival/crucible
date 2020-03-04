------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.ArraySizeProfile
-- Description      : Execution feature to observe argument buffer sizes
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Samuel Breese <sbreese@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# Options -Wall #-}
{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language ViewPatterns #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language TypeFamilies #-}

module Lang.Crucible.LLVM.ArraySizeProfile
 ( FunProfile(..), funProfileName, funProfileArgs
 , ArgProfile(..), argProfileSize, argProfileInitialized
 , arraySizeProfile
 ) where

import Control.Lens.TH

import Control.Lens

import Data.Type.Equality
import Data.Foldable
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import Data.Map (Map)
import qualified Data.Map as Map

import Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C

import qualified Lang.Crucible.LLVM.Extension as C
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.Translation.Monad as C

import qualified What4.Interface as W4

------------------------------------------------------------------------
-- Profiles

data ArgProfile = ArgProfile
  { _argProfileSize :: Maybe Int
  , _argProfileInitialized :: Bool
  } deriving (Show, Eq, Ord)
makeLenses ''ArgProfile

data FunProfile = FunProfile
  { _funProfileName :: Text
  , _funProfileArgs :: [ArgProfile]
  } deriving (Show, Eq, Ord)
makeLenses ''FunProfile

------------------------------------------------------------------------
-- Learning a profile from an ExecState

ptrStartsAlloc ::
  W4.IsExpr (W4.SymExpr sym) =>
  C.LLVMPtr sym w ->
  Bool
ptrStartsAlloc (C.llvmPointerView -> (_, W4.asUnsignedBV -> Just 0)) = True
ptrStartsAlloc _ = False

ptrAllocSize ::
  forall sym w. W4.IsExpr (W4.SymExpr sym) =>
  [G.MemAlloc sym] ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrAllocSize mem (C.llvmPointerView -> (blk, _)) = msum $ inAlloc <$> mem
  where inAlloc :: G.MemAlloc sym -> Maybe Int
        inAlloc memAlloc
          | G.Alloc _ a (Just sz) _ _ _ <- memAlloc
          , Just a == W4.asNat blk =
            fromIntegral <$> W4.asUnsignedBV sz
          | otherwise = Nothing

ptrArraySize ::
  W4.IsExpr (W4.SymExpr sym) =>
  [G.MemAlloc sym] ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrArraySize mem ptr
  | ptrStartsAlloc ptr = ptrAllocSize mem ptr
  | otherwise = Nothing

intrinsicArraySize ::
  W4.IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  SymbolRepr nm ->
  C.CtxRepr ctx ->
  C.Intrinsic sym nm ctx ->
  Maybe Int
intrinsicArraySize mem
  (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  (Ctx.Empty Ctx.:> C.BVRepr _w) i = ptrArraySize mem i
intrinsicArraySize _ _ _ _ = Nothing

regValueArraySize ::
  W4.IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  C.TypeRepr tp ->
  C.RegValue sym tp ->
  Maybe Int
regValueArraySize mem (C.IntrinsicRepr nm ctx) i = intrinsicArraySize mem nm ctx i
regValueArraySize _ _ _ = Nothing

regEntryArraySize ::
  W4.IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  C.RegEntry sym tp ->
  Maybe Int
regEntryArraySize mem (C.RegEntry t v) = regValueArraySize mem t v

newtype Wrap a (b :: C.CrucibleType) = Wrap { unwrap :: a }
argProfiles ::
  W4.IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  [ArgProfile]
argProfiles mem as = uncurry ArgProfile <$>
  ( zip (Vector.toList $ Ctx.toVector (fmapFC (Wrap . regEntryArraySize mem) as) unwrap)
    $ repeat False
  )

------------------------------------------------------------------------
-- Execution feature for learning profiles

updateProfiles ::
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunProfile]) ->
  C.ExecState p sym (C.LLVM arch) rtp ->
  IO ()
updateProfiles llvm cell state
  | C.CallState _ (C.CrucibleCall _ frame) sim <- state
  , C.CallFrame { C._frameCFG = cfg, C._frameRegs = regs } <- frame
  , Just mem <- C.memImplHeap <$> C.lookupGlobal (C.llvmMemVar llvm)
                (sim ^. C.stateTree . C.actFrame . C.gpGlobals)
  = do
      modifyIORef' cell $ \profs ->
        let name = Text.pack . show $ C.cfgHandle cfg
            argProfs = argProfiles (G.memAllocs mem) $ C.regMap regs
            funProf = FunProfile name argProfs
        in case Map.lookup name profs of
             Nothing -> Map.insert name [funProf] profs
             Just variants
               | funProf `elem` variants -> profs
               | otherwise -> Map.insert name (funProf:variants) profs
  | otherwise = pure ()

arraySizeProfile ::
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunProfile]) ->
  IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
arraySizeProfile llvm cell = do
  pure . C.ExecutionFeature $ \s -> do
    updateProfiles llvm cell s
    pure C.ExecutionFeatureNoChange
