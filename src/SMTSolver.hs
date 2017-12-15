module SMTSolver where

import Parser

import Text.Parsec hiding (crlf)
import Text.Parsec.String
import System.IO
import System.Exit
import System.Process
import Data.List.Split (splitOn)
import Control.Monad


-- Solver-related data structures

data SolverConfig = SolverConfig {
  solverArgs :: String,
  dRealVersion :: Int,
  dRealPath :: String
} deriving (Show, Eq)


-- Call solver
run :: SolverConfig -> String -> Double -> IO String
run sconf f delta = do
    let p = (shell (dRealPath sconf ++ " " ++ f ++ " --model --precision " ++ show delta ++ " " ++ solverArgs sconf))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out


-- Parsing utilities for solver response
parseDRealResponse :: Int -> Parser Response
parseDRealResponse v = do
  let p = case v of
        3 -> parseDReal3Var
        4 -> parseDReal4Var
  vs <- many p
  return $ Response "sat" vs -- This got weird with the addition of dreal4...

parseDRealSat :: Int -> String -> Response
parseDRealSat v s = case splitOn "\n" s of
  ("unsat"):_ -> Response "unsat" []
  strs ->
    let strs' = case v of
         3 -> tail $ rmLast (rmLast strs)
         4 -> tail (rmLast strs)
    in case parse (parseDRealResponse v <* eof) "" (join strs') of
      Left err -> error $ show err
      Right v -> v

rmLast :: [a] -> [a]
rmLast [] = []
rmLast [x] = []
rmLast xs = init xs
