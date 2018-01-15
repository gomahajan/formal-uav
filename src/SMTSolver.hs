module SMTSolver where

import Parser

import Text.Parsec hiding (crlf)
import Text.Parsec.String
import System.IO
import System.Exit
import System.Process
import Data.List.Split (splitOn)
import Control.Monad
import Debug.Trace


-- Solver-related data structures
data SolverConfig = SolverConfig {
  solverArgs :: String,
  dRealVersion :: Int,
  dRealPath :: String,
  z3Path :: String
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
genSolverCallZ3 sconf f delta = z3Path sconf ++ " " ++ f

-- Parsing utilities for solver response

nonWhitespace = many $ noneOf " \t\n"

parseZ3Var :: Parser Assignment
parseZ3Var = do
  string "("
  whitespace
  s <- nonWhitespace
  whitespace
  x <- try parseRational <|> try parseSci <|> try parseDouble <|> parseDInt
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

parsePair :: Parser (Double, Double)
parsePair = do
  whitespace
  x <- parseNum
  char ','
  whitespace
  y <- parseNum
  whitespace
  return (x, y)

-- Place holder return values for now.
-- TODO: find max/min double to use as pair. Though currently we just grab one
-- of the extremal values from the cx pair....?
parseEntire :: Parser (Double, Double)
parseEntire = do
  whitespace
  string "ENTIRE"
  whitespace
  return (0.0, 0.0)

parseDRealRange :: Parser (Double, Double)
parseDRealRange = do
  whitespace
  char '['
  xs <- try parseEntire <|> parsePair
  char ']'
  whitespace
  return xs 

parseDRealResponse :: Int -> Parser Response
parseDRealResponse v = do
  let p = case v of
        2 -> error $ "Incorrect solver parser"
        3 -> parseDReal3Var
        4 -> parseDReal4Var
  vs <- many p
  return $ Response "sat" vs -- This got weird with the addition of dreal4...

parseZ3Response :: Parser Response
parseZ3Response = do
  void.many $ letter
  char '('
  vs <- many parseZ3Var
  char ')'
  return $ Response "sat" vs

parseDRealSat :: Int -> String -> Response
parseDRealSat v s = case splitOn "\n" s of
  ("unsat"):_ -> Response "unsat" []
  strs ->
    let (strs', respParser) = case v of
         2 -> (tail strs, parseZ3Response)
         3 -> (tail $ rmLast (rmLast strs), parseDRealResponse 3)
         4 -> (tail (rmLast strs), parseDRealResponse 4)
    in case parse (respParser <* eof) "" (join strs') of
            Left err -> traceShow (join strs') $ error $ show err
            Right v -> v

rmLast :: [a] -> [a]
rmLast [] = []
rmLast [x] = []
rmLast xs = init xs
