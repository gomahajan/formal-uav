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

parseDRealVar :: Parser Assignment
parseDRealVar = do
  s <- nonWhitespace
  whitespace
  string ": [ ENTIRE ] = ["
  whitespace
  x <- try parseDouble <|> parseInt
  char ','
  whitespace
  y <- try parseDouble <|> parseInt
  char ']'
  whitespace
  return (s, x) -- TODO: be smarter about which val to return

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
  x <- many1 digit
  return $ fst . head $ readFloat x

parseDouble :: Parser Double
parseDouble = do
  x <- many1 digit
  char '.'
  y <- many1 digit
  return $ fst . head $ readFloat (x ++ "." ++ y)

parseDRealResponse :: Parser Response
parseDRealResponse = do
  s <- many1 letter
  char ':'
  whitespace
  vs <- many parseDRealVar
  return $ Response s vs

parseResponse :: Parser Response
parseResponse = do
  s <- many1 letter
  whitespace
  vs <- many parseVar
  return $ Response s vs

-- For Z3
parseSat :: String -> Response
parseSat s = case parse (parseResponse <* eof) "" s of
  Left err -> error $ show $ Parser err
  Right v -> v

parseDRealSat :: String -> Response
parseDRealSat s = case splitOn "\n" s of
  ("unsat"):_ -> Response "unsat" []
  strs -> trace ("\n\n" ++ (join (rmLast (rmLast strs))) ++ "\n\n") $ case parse (parseDRealResponse <* eof) "" (join (rmLast (rmLast strs))) of
      Left err -> error $ show $ Parser err
      Right v -> v

rmLast::[a]->[a]
rmLast [] = []
rmLast [x] = []
rmLast xs = init xs
