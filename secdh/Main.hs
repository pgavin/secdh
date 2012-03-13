module Main where

import Control.Monad
import qualified Data.Map as Map
import Data.List

import System.Environment
import System.IO
import System.Exit

import Language.Slambda.Types
import Language.Slambda.Read
import Language.Slambda.Show

import SECDH.Types
import SECDH.Show
import SECDH.Eval

getPrograms :: [FilePath] -> IO Program
getPrograms fs = do
  fmap concat $ mapM getProgram fs
  where getProgram f = do
          c <- readFile f
          case parseProgram c of
            Just p ->
              return p
            Nothing -> 
              error $ "error parsing " ++ f

main :: IO ()
main = do
  args <- getArgs
  progName <- getProgName
  let (stats, files) =
        case args of
          ("-s":args') -> (True, args')
          _           -> (False, args)
  if null files
    then do hPutStrLn stderr $ "usage: " ++ progName ++ " [-s] file.slam ..."
            exitFailure
    else do p <- getPrograms files
            let secdh0 = secdhInitProgram p
            if stats
              then do (secdh, r, stats) <- secdhFinishStats secdh0
                      printStats stats
                      printResult r
              else do r <- secdhEval p
                      hPutStrLn stderr $ atomToString r

printStatesAndRules :: [(SECDH, Rule)] -> IO ()
printStatesAndRules = printStates' 1
  where printStates' n [] = return ()
        printStates' n ((secdh, rule):secdhAndRules) = do
          hPutStrLn stderr ""
          hPutStrLn stderr $ "State " ++ show n ++ ":"
          hPutStrLn stderr $ secdhToString secdh
          hPutStrLn stderr $ "Rule to be applied: " ++ show (ruleNum rule)
          printStates' (succ n) secdhAndRules

printResult :: Atom -> IO ()
printResult =
  hPutStrLn stderr . showString "Result: " . atomToString

printStats :: SECDHStats -> IO ()
printStats (SECDHStats iters maxStack maxEnv maxControl maxDump maxHeap maxRetained gcs ruleExecs) = do
  sequence_ [ do hPutStr stderr (l ++ ": ")
                 let nl = length l
                     nv = length v
                 when (nl < maxStatLabel) $ do
                   hPutStr stderr (replicate (maxStatLabel - nl) ' ')
                 when (nv < maxStatVal) $ do
                   hPutStr stderr (replicate (maxStatVal - nv) ' ')
                 hPutStrLn stderr v
            | (l, v) <- stats ]
  where stats = [ ( "Iterations"       , show iters       )
                , ( "Max Stack Size"   , show maxStack    )
                , ( "Max Env Size"     , show maxEnv      )
                , ( "Max Control Size" , show maxControl  )
                , ( "Max Dump Size"    , show maxDump     )
                , ( "Max Heap Size"    , show maxHeap     )
                , ( "Max Retained"     , show maxRetained )
                , ( "GCs"              , show gcs         ) ] ++
                [ ( "Rule " ++ show r  , show n           ) | (Rule r, n) <- Map.assocs ruleExecs ]
        maxStatLabel = foldl' max 0 (map (length . fst) stats)
        maxStatVal   = foldl' max 0 (map (length . snd) stats)
