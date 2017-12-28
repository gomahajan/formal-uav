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
run :: Int -> SolverConfig -> String -> Double -> IO String
run n sconf f delta = do
    let solver = case n of
                  2 -> genSolverCallZ3
                  3 -> genSolverCall
                  4 -> genSolverCall
    let p = (shell (solver sconf f delta))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out

genSolverCall :: SolverConfig -> String -> Double -> String
genSolverCall sconf f delta = dRealPath sconf ++ " " ++ f ++ " --model --precision " ++ show delta ++ " " ++ solverArgs sconf

genSolverCallZ3 :: SolverConfig -> String -> Double -> String
genSolverCallZ3 sconf f delta = "z3win\\bin\\z3" ++ " " ++ f

-- Parsing utilities for solver response

nonWhitespace = many $ noneOf " \t\n"

parseVar :: Parser Assignment
parseVar = do
  string "("
  whitespace
  s <- many1 (letter <|> digit <|> oneOf "_")
  whitespace
  x <- try parseRational <|> parseSci <|> try parseDouble <|> parseDInt
  whitespace
  string ")"
  whitespace
  return (s, x)

-- Placeholders until specification language parser is done
parseDReal4Var :: Parser Assignment
parseDReal4Var = do
  s <- nonWhitespace
  whitespace
  char ':'
  (x,y) <- parseDRealRange
  return (s,x)

parseDReal3Var :: Parser Assignment
parseDReal3Var = do
  s <- nonWhitespace
  whitespace
  string ": [ ENTIRE ] ="
  (x,y) <- parseDRealRange
  return (s, x) -- TODO: be smarter about which val to return

parseDRealRange :: Parser (Double, Double)
parseDRealRange = do
  whitespace
  char '['
  whitespace
  x <- parseNum
  char ','
  whitespace
  y <- parseNum
  char ']'
  whitespace
  return (x,y)

parseDRealResponse :: Int -> Parser Response
parseDRealResponse v = do
  let p = case v of
        2 -> parseVar
        3 -> parseDReal3Var
        4 -> parseDReal4Var
  vs <- many p
  return $ Response "sat" vs -- This got weird with the addition of dreal4...

parseDRealSat :: Int -> String -> Response
parseDRealSat v s = case splitOn "\n" s of
  ("unsat"):_ -> Response "unsat" []
  strs ->
    let strs' = case v of
         2 -> tail strs
         3 -> tail $ rmLast (rmLast strs)
         4 -> tail (rmLast strs)
    in case parse (parseDRealResponse v <* eof) "" (tail (rmLast (join strs'))) of
            Left err -> error $ show err
            Right v -> v

rmLast :: [a] -> [a]
rmLast [] = []
rmLast [x] = []
rmLast xs = init xs
