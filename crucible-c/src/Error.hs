{-# Language ExistentialQuantification #-}
module Error (module Error, catch) where

import Control.Monad.IO.Class(MonadIO, liftIO)
import Control.Exception(Exception(..), SomeException(..), throwIO, catch)
import Data.Typeable(cast)
import qualified Data.Text as Text

import Data.LLVM.BitCode (formatError)
import qualified Data.LLVM.BitCode as LLVM


import Lang.Crucible.ProgramLoc(ProgramLoc,plSourceLoc,Position(..))
import Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..))
import Lang.Crucible.Simulator.SimError
          (SimError(..), SimErrorReason(..),ppSimError,simErrorReasonMsg,simErrorReason)

import Lang.Crucible.LLVM.Extension(LLVM)

throwError :: MonadIO m => Error -> m a
throwError x = liftIO (throwIO x)

data Error =
    LLVMParseError LLVM.Error
  | FailedToProve ProgramLoc
                  (Maybe SimErrorReason)
                  (Maybe String) -- Counter example as C functions.
  | forall b arch.
      SimFail (AbortedResult b (LLVM arch))
  | BadFun
  | MissingFun String
  | Bug String
  | ClangError Int String String
  | EnvError String

instance Show Error where
  show = show . ppError

instance Exception Error where
  toException      = SomeException
  fromException (SomeException e) = cast e
  displayException = ppError

ppError :: Error -> String
ppError err =
  case err of
    LLVMParseError e -> formatError e
    FailedToProve loc mb _ -> docLoc ++ txt
      where
      docLoc =
        case plSourceLoc loc of
          SourcePos f l c ->
            Text.unpack f ++ ":" ++ show l ++ ":" ++ show c ++ " "
          _ -> ""
      txt = case mb of
              Nothing -> "Assertion failed." -- shouldn't happen
              Just s  -> simErrorReasonMsg s
    SimFail (AbortedExec e _)
      | AssertFailureSimError x <- simErrorReason e -> x
    SimFail x -> unlines ["Error during simulation:", ppErr x]
    BadFun -> "Function should have no arguments"
    MissingFun nm -> "Cannot find code for " ++ show nm
    Bug x -> x
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]
    EnvError msg -> msg

ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec (SimError _ InfeasibleBranchError) _gp -> "Assumptions too strong (dead code)"
    AbortedExec err _gp -> show (ppSimError err)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"


