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

-- Parse a variable assignment from z3
parseVar :: Parser Assignment
parseVar = do
  string "(("
  whitespace
  s <- many1 (letter <|> digit)
  whitespace
  x <- many1 digit
  char '.'
  y <- many1 digit
  whitespace
  string "))"
  whitespace
  return (s, fst . head $ readFloat (x ++ "." ++ y))

--parseDRealVar :: Parser Assignment

parseResponse :: Parser Response
parseResponse = do
  s <- many1 letter
  whitespace
  vs <- many parseVar
  return $ Response s vs

parseSat :: String -> ThrowsError Response
parseSat s = case parse (parseResponse <* eof) "" s of
  Left err -> throwError $ Parser err
  Right v -> return v
