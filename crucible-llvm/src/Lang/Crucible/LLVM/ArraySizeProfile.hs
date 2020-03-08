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
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language PatternSynonyms #-}
{-# Language BangPatterns #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language TypeFamilies #-}
{-# Language GADTs #-}

module Lang.Crucible.LLVM.ArraySizeProfile
 ( FunProfile(..), funProfileName, funProfileArgs
 , ArgProfile(..), argProfileSize, argProfileInitialized
 , arraySizeProfile
 ) where

import Control.Lens.TH

import System.IO

import Control.Monad
import Control.Lens

import Data.Type.Equality
import Data.Foldable
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Parameterized.Some
import Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import qualified Lang.Crucible.Analysis.Fixpoint as C
import qualified Lang.Crucible.Analysis.Fixpoint.Components as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Types as C

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
-- Generalize loops

type WTOMap = Map Int (Int, Int)

buildWTOMap :: [C.WTOComponent (Some (C.BlockID blocks))] -> WTOMap
buildWTOMap = snd . go 0 0 Map.empty
  where
    go :: Int -> Int -> WTOMap -> [C.WTOComponent (Some (C.BlockID blocks))] -> (Int, WTOMap)
    go !x !_ m [] = (x, m)
    go !x !d m (C.Vertex (Some bid):cs) =
       let m' = Map.insert (Ctx.indexVal $ C.blockIDIndex bid) (x, d) m
       in go (x + 1) d m' cs
    go !x !d m (C.SCC (Some hd) subcs : cs) =
       let m' = Map.insert (Ctx.indexVal $ C.blockIDIndex hd) (x, d + 1) m
           (x', m'') = go (x + 1) (d + 1) m' subcs
       in go x' d m'' cs

isBackedge ::
  WTOMap ->
  Some (C.BlockID blocks) ->
  C.BlockID blocks args ->
  Bool
isBackedge wtoMap (Some current) target
  | Just (cx, _) <- Map.lookup (Ctx.indexVal $ C.blockIDIndex current) wtoMap
  , Just (tx, _) <- Map.lookup (Ctx.indexVal $ C.blockIDIndex target) wtoMap
  , tx <= cx
  = True
  | otherwise = False

generalizeMemory ::
  G.Mem sym {- ^ Old memory -} ->
  G.Mem sym {- ^ New memory -} ->
  IO (Maybe (G.Mem sym)) {- ^ Nothing if old memory already generalizes new memory -}
generalizeMemory _old new = do
  putStrLn "generalizing..."
  pure $ Just new

debugState :: C.ExecState p sym ext rtp -> String
debugState C.ResultState{} = "Result"
debugState C.AbortState{} = "Abort"
debugState C.UnwindCallState{} = "UnwindCall"
debugState C.CallState{} = "Call"
debugState C.TailCallState{} = "TailCall"
debugState C.ReturnState{} = "Return"
debugState C.RunningState{} = "Running"
debugState C.SymbolicBranchState{} = "SymbolicBranch"
debugState C.ControlTransferState{} = "ControlTransfer"
debugState C.OverrideState{} = "Override"
debugState C.BranchMergeState{} = "BranchMerge"
debugState C.InitialState{} = "InitialState"

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
  , Just mem <- C.memImplHeap <$> C.lookupGlobal (C.llvmMemVar llvm) (sim ^. C.stateGlobals)
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
  forall sym arch p rtp.
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunProfile]) ->
  IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
arraySizeProfile llvm profiles = do
  (frameLoopStarts :: IORef (Map Text (Set Int))) <- newIORef Map.empty
  (frameWTOMaps :: IORef (Map Text WTOMap)) <- newIORef Map.empty
  (frameMemCache :: IORef (Map Text (G.Mem sym))) <- newIORef Map.empty
  pure . C.ExecutionFeature $ \s -> do
    hPutStrLn stderr $ debugState s
    updateProfiles llvm profiles s
    case s of
      C.CallState _ (C.CrucibleCall _ C.CallFrame { C._frameCFG = g }) _ -> do
        let name = Text.pack . show $ C.cfgHandle g
        let wtoMap = buildWTOMap $ C.cfgWeakTopologicalOrdering g
        modifyIORef frameWTOMaps $ \fwto ->
          case Map.lookup name fwto of
            Just _ -> fwto
            Nothing -> Map.insert name wtoMap fwto
        pure C.ExecutionFeatureNoChange
      C.RunningState (C.RunBlockStart bid) st -> do
        frameStarts <- readIORef frameLoopStarts
        let name = Text.pack . show . C.frameHandle $ st ^. C.stateCrucibleFrame
        case Map.lookup name frameStarts of
          Just starts
            | Set.member (Ctx.indexVal $ C.blockIDIndex bid) starts
            , Just memImpl <- C.lookupGlobal (C.llvmMemVar llvm) (st ^. C.stateGlobals)
              -> do
                fmc <- readIORef frameMemCache
                case Map.lookup name fmc of
                  Just oldMem -> generalizeMemory oldMem (C.memImplHeap memImpl) >>= \case
                    Just genMem -> do
                      writeIORef frameMemCache $ Map.insert name genMem fmc
                      let st' = st & C.stateGlobals
                            %~ C.insertGlobal (C.llvmMemVar llvm) memImpl { C.memImplHeap = genMem }
                      pure . C.ExecutionFeatureModifiedState
                        $ C.RunningState (C.RunBlockStart bid) st'
                    Nothing ->
                      -- TODO: quit loop
                      pure C.ExecutionFeatureNoChange
                  _ -> do
                    writeIORef frameMemCache $ Map.insert name (C.memImplHeap memImpl) fmc
                    pure C.ExecutionFeatureNoChange
          _ -> pure C.ExecutionFeatureNoChange
      C.ControlTransferState (C.ContinueResumption (C.ResolvedJump target _)) st ->
        transition frameLoopStarts frameWTOMaps target st
      C.ControlTransferState (C.CheckMergeResumption (C.ResolvedJump target _)) st ->
        transition frameLoopStarts frameWTOMaps target st
      _ -> pure C.ExecutionFeatureNoChange
  where
    transition frameLoopStarts frameWTOMaps target st = do
      let name = Text.pack . show . C.frameHandle $ st ^. C.stateCrucibleFrame
      fwto <- readIORef frameWTOMaps
      case Map.lookup name fwto of
        Just wtoMap
          | isBackedge wtoMap (st ^. C.stateCrucibleFrame . C.frameBlockID) target
            -> modifyIORef frameLoopStarts
               $ Map.alter
               ( \case
                   Just s -> Just $ Set.insert (Ctx.indexVal $ C.blockIDIndex target) s
                   Nothing -> Just . Set.singleton . Ctx.indexVal $ C.blockIDIndex target
               ) name
        _ -> pure ()
      pure C.ExecutionFeatureNoChange
