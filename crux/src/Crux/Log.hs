{-# LANGUAGE ImplicitParams #-}
-- from crucible-c/src/Log.hs
module Crux.Log (
  -- * Configuring output
  OutputConfig(..), showColors, outputHandle, errorHandle, defaultOutputConfig,
  -- * Performing output
  say, sayOK, sayFail, output, outputLn
  ) where

import Control.Exception (bracket_)
import Control.Lens

import System.Console.ANSI
import System.IO

-- | Global options for Crux's main. These are not CruxOptions because
-- they are expected to be set directly by main, rather than by a
-- user's command-line options. They exist primarily to improve the
-- testability of the code.
data OutputConfig =
  OutputConfig { _showColors :: Bool
               , _outputHandle :: Handle
               , _errorHandle :: Handle
               }

showColors :: Lens' OutputConfig Bool
showColors = lens _showColors (\ o s -> o { _showColors = s })

outputHandle :: Lens' OutputConfig Handle
outputHandle = lens _outputHandle (\ o h -> o { _outputHandle = h })

errorHandle :: Lens' OutputConfig Handle
errorHandle = lens _errorHandle (\ o h -> o { _errorHandle = h })

defaultOutputConfig :: OutputConfig
defaultOutputConfig = OutputConfig True stdout stderr


output :: (?outputConfig :: OutputConfig) => String -> IO ()
output str = hPutStr (view outputHandle ?outputConfig) str

outputLn :: (?outputConfig :: OutputConfig) => String -> IO ()
outputLn str = hPutStrLn (view outputHandle ?outputConfig) str

outputColored :: (?outputConfig :: OutputConfig) => Color -> String -> IO ()
outputColored c msg =
  let outH = view outputHandle ?outputConfig
      inColor = view showColors ?outputConfig
  in if inColor
       then bracket_
              (hSetSGR outH [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c])
              (hSetSGR outH [Reset])
              (hPutStr outH msg)
       else output msg

sayOK :: (?outputConfig :: OutputConfig) => String -> String -> IO ()
sayOK = sayCol Green

sayFail :: (?outputConfig :: OutputConfig) => String -> String -> IO ()
sayFail = sayCol Red

say :: (?outputConfig :: OutputConfig) => String -> String -> IO ()
say x y = outputLn ("[" ++ x ++ "] " ++ y)

sayCol ::  (?outputConfig :: OutputConfig) => Color -> String -> String -> IO ()
sayCol col x y =
  do output "["
     outputColored col x
     output ("] " ++ y)


