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

parseDRealVar :: Parser Assignment
parseDRealVar = do
  s <- many1 (letter <|> digit)
  whitespace
  string ": [ ENTIRE ] = ["
  whitespace
  x <- parseDouble
  char ','
  whitespace
  y <- parseDouble
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

parseDouble :: Parser Double
parseDouble = do
  x <- many1 digit
  char '.'
  y <- many1 digit
  return $ fst . head $ readFloat (x ++ "." ++ y)

parseDRealResponse :: Parser Response
parseDRealResponse = do
  s <- many1 letter
  whitespace
  vs <- many parseDRealVar
  return $ Response s vs

parseResponse :: Parser Response
parseResponse = do
  s <- many1 letter
  whitespace
  vs <- many parseVar
  return $ Response s vs

parseSat :: String -> Response
parseSat s = case parse (parseDRealResponse <* eof) "" s of
  Left err -> error $ show $ Parser err
  Right v -> v
