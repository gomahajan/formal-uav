module Parser where

import Control.Monad
import Text.Parsec hiding (crlf)
import Text.Parsec.String
import Text.Parsec.Token as Token
import Control.Applicative ((<*))
import Debug.Trace
import Control.Monad.Except
import System.IO
import Numeric
import Data.Map

import Logic
import CodeGen

type Assignment = (String, Double)

data Response = Response String [Assignment] deriving (Show)

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"

nonWhitespace = many $ noneOf " \t\n"

-- Various number formats
parseNum = try parseSci <|> try parseDouble <|> parseDInt

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

--Specification language parsers

parseDynamics :: Char -> Parser ODE
parseDynamics c = do
  string "d/dt["
  whitespace
  char c
  whitespace
  char ']'
  whitespace
  char '='
  whitespace
  --de <- parseODE
  --return de
  return $ EVar "temp"

-- Parse constant definitions
parseDef :: Parser (String, Double)
parseDef = do
  string "#define"
  whitespace
  s <- nonWhitespace
  whitespace
  v <- parseNum
  whitespace
  return (s, v)

parseDomain :: Parser (String, Domain)
parseDomain = do
  string "#domain"
  whitespace
  v <- nonWhitespace
  whitespace
  char '['
  x <- parseNum
  whitespace
  char ','
  whitespace
  y <- parseNum
  whitespace
  char ']'
  whitespace
  return (v, Domain { vmin = x, vmax = y } )

-- Tokens
unOpTokens :: Map UnOp String
unOpTokens = fromList [ (Neg, "-")
                      , (Sin, "sin")
                      , (Cos, "cos")
                      , (Tan, "tan")
                      ]

binOpTokens :: Map BinOp String
binOpTokens = fromList [ (Times,     "*")
                       , (Plus,      "+")
                       , (Minus,     "-")
                       , (Div,       "/")
                       , (Pow,       "^")
                       , (Eq,        "==")
                       , (Lt,        "<")
                       , (Leq,        "<=")
                       , (Gt,        ">")
                       , (Geq,        ">=")
                       ]
