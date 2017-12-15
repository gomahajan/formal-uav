module Parser where
import Control.Monad
import Text.Parsec hiding (crlf)
import Text.Parsec.String
import Control.Applicative ((<*))
import Debug.Trace
import Control.Monad.Except
import System.IO
import Numeric
import Data.List.Split (splitOn)

import Logic


type Assignment = (String, Double)

data Response = Response String [Assignment] deriving (Show)

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"

nonWhitespace = many $ noneOf " \t\n"

-- Various number formats
parseNum = try parseSci <|> try parseDouble <|> parseInt


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

-- Parse a variable assignment from z3
parseVar :: Parser Assignment
parseVar = do
  string "(("
  whitespace
  s <- many1 (letter <|> digit)
  whitespace
  x <- parseDouble
  whitespace
  string "))"
  whitespace
  return (s, x)

parseInt :: Parser Double -- still represented as a double lol
parseInt = do
  sign <- many $ char '-'
  x <- many1 digit
  let val = fst . head $ readFloat x
  return $ case sign of
    [] -> val
    _  -> (-1) * val

parseDouble :: Parser Double
parseDouble = do
  sign <- many $ char '-'
  x <- many1 digit
  char '.'
  y <- many1 digit
  let val = fst . head $ readFloat (x ++ "." ++ y)
  return $ case sign of
    [] -> val
    _  -> (-1) * val

-- Parser for doubles in scientific notation
parseSci :: Parser Double
parseSci = do
  base <- try parseDouble <|> parseInt
  char 'e'
  ms <- many $ char '-'
  ex <- many1 digit
  let pwr = read ex
  return $ case ms of
    [] -> base * (10 ^ pwr)
    _ -> base / (10 ^ pwr)

parseDRealResponse :: Int -> Parser Response
parseDRealResponse v = do
  let p = case v of
        3 -> parseDReal3Var
        4 -> parseDReal4Var
  vs <- many p
  return $ Response "sat" vs -- This got weird with the addition of dreal4...

parseResponse :: Parser Response
parseResponse = do
  s <- many1 letter
  whitespace
  vs <- many parseVar
  return $ Response s vs

-- For Z3
-- TODO: remove z3
parseSat :: String -> Response
parseSat s = case parse (parseResponse <* eof) "" s of
  Left err -> error $ show $ Parser err
  Right v -> v

parseDRealSat :: Int -> String -> Response
parseDRealSat v s = case splitOn "\n" s of
  ("unsat"):_ -> Response "unsat" []
  strs ->
    let strs' = case v of
         3 -> tail $ rmLast (rmLast strs)
         4 -> tail (rmLast strs)
    in case parse (parseDRealResponse v <* eof) "" (join strs') of
      Left err -> error $ show $ Parser err
      Right v -> v

rmLast :: [a] -> [a]
rmLast [] = []
rmLast [x] = []
rmLast xs = init xs
