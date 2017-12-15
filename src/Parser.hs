module Parser where

import Control.Monad
import Text.Parsec hiding (crlf)
import Text.Parsec.String
import Control.Applicative ((<*))
import Debug.Trace
import Control.Monad.Except
import System.IO
import Numeric

import Logic

type Assignment = (String, Double)

data Response = Response String [Assignment] deriving (Show)

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"

nonWhitespace = many $ noneOf " \t\n"

-- Various number formats
parseNum = try parseSci <|> try parseDouble <|> parseDInt

-- parser for ints from dreal response (represented as doubles for convenience)
parseDInt :: Parser Double
parseDInt = do
  sign <- many $ char '-'
  x <- many1 digit
  let val = fst . head $ readFloat x
  return $ case sign of
    [] -> val
    _  -> (-1) * val

-- Decimal doubles
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
  base <- try parseDouble <|> parseDInt
  char 'e'
  ms <- many $ char '-'
  ex <- many1 digit
  let pwr = read ex
  return $ case ms of
    [] -> base * (10 ^ pwr)
    _ -> base / (10 ^ pwr)

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


--Specification language parsers
