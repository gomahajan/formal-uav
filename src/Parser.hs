module Parser where

import Control.Monad
import Text.Parsec hiding (crlf)
import Text.Parsec.String
import qualified Text.Parsec.Token as Token
import Text.Parsec.Expr as Expr
import Control.Applicative ((<*))
import Debug.Trace
import Control.Monad.Except
import System.IO
import Numeric
import qualified Data.Map as Map
import Data.Map (Map, empty)
import Data.List

import Logic
import CodeGen

type Assignment = (String, Double)

data Response = Response String [Assignment] deriving (Show)

parseFromFile :: Parser a -> String -> IO (Either ParseError a)
parseFromFile parser fname = do
  input <- readFile fname
  return $ parse parser fname input

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"
onelineWS = void . many $ oneOf " \t"

-- debugging helper
println msg = trace (show msg) $ return ()

ignore = do
  whitespace
  skipMany comment <?> "comment"
  whitespace

name = many1 $ noneOf " ()\t\n:#=[]*/&|{}"

comment :: Parser String
comment = do
  onelineWS
  string "//"
  s <- manyTill anyChar newline
  return s

-- Various number formats
parseNum = do
  x <- try parseSci <|> try parseDouble <|> parseDInt
  ignore
  return x

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

-- Rationals
parseRational :: Parser Double
parseRational = do
  string "(/"
  whitespace
  num <- parseDouble
  whitespace
  den <- parseDouble
  whitespace
  string ")"
  return $ num / den

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

parseInt = read <$> many1 digit

-- Specification language parsers

-- Parses complete specification
parseDecls :: Parser Decls
parseDecls = do
  ignore
  defs <- many $ try parseDef
  ignore
  doms <- many $ try parseDomain
  ignore
  params <- try parseParams <|> return defaultPs <?> "initial parameters"
  modes <- try parseCD <|> return [] <?> "relational dynamics"
  ignore
  vars <- try parseEnv <|> return [] <?> "environment"
  ignore
  string "#uav" -- uav dynamics
  ignore
  uavms <- many1 (try parseUAV) <?> "uav dynamics"
  s <- many1 (try parseSensor) <?> "sensor definition"
  ignore
  string "#invariant"
  ignore
  inv <- parsePred
  ignore
  let modes' = case modes of
       [] -> [Mode {modeId = 0, uavMode = "charge", sensorMode = "collect"}
            , Mode {modeId = 1, uavMode = "fly_to", sensorMode = "collect"}
            , Mode {modeId = 2, uavMode = "download", sensorMode = "upload"}
            , Mode {modeId = 3, uavMode = "fly_back", sensorMode = "collect"}]
       m  -> m
  return Decls {
    _defns = Map.fromList defs,
    _varDomains = Map.fromList doms,
    _modeDefs = modes',
    _uavModes = uavms,
    _sensors = s,
    _environment = vars,
    _numHoles = length params,
    _invt = convert inv,
    _paramValues = params
  }
    where
      defaultPs = [("p0",9), ("p1",9), ("p2",10), ("p3",1), ("p4",9), ("p5",9), ("p6",10), ("p7",1), ("p8",9), ("p9",9)]


opNames :: [String]
opNames = Map.elems unOpTokens ++ Map.elems binOpTokens ++ ["//"]

opStart :: String
opStart = nub (fmap head opNames)

opLetter :: String
opLetter = nub (concatMap tail opNames)

specLang :: Token.LanguageDef ()
specLang = Token.LanguageDef
  ""
  ""
  "//"
  False
  letter
  alphaNum
  (oneOf Parser.opStart)
  (oneOf Parser.opLetter)
  []
  opNames
  True

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser specLang

parens = Token.parens lexer

parseEnv :: Parser [(String, Pred)]
parseEnv = do
  whitespace
  string "#variables"
  ignore
  vars <- many1 $ try parseVar
  ignore
  return vars

parseConst :: Parser (String, Double)
parseConst = do
  whitespace
  s <- name
  whitespace
  v <- parseNum
  ignore
  return (s,v)

parseVar :: Parser (String, Pred)
parseVar = do
  whitespace
  s <- name
  whitespace
  char '='
  whitespace
  v <- parsePred
  whitespace
  return (s,v)

parseHoles :: Parser Int
parseHoles = do
  whitespace
  string "num_holes"
  whitespace
  char '='
  whitespace
  ns <- many1 digit
  ignore
  return $ read ns

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
  de <- parseODE
  return de
  --return $ EVar "temp"

-- Parse constant definitions
parseDef :: Parser (String, Double)
parseDef = do
  string "#define"
  parseConst

parseDomain :: Parser (String, Domain)
parseDomain = do
  string "#domain"
  whitespace
  v <- name
  whitespace
  char '['
  whitespace
  x <- many parseNum
  whitespace
  char ','
  whitespace
  y <- many parseNum
  whitespace
  char ']'
  ignore
  let x' = case x of
             [] -> Nothing
             xs -> Just $ head xs
      y' = case y of
             [] -> Nothing
             ys -> Just $ head ys
  return (v, Domain { vmin = x', vmax = y' } )

parseParams :: Parser [(String, Double)]
parseParams = do
  whitespace
  string "#params"
  ignore
  vs <- many $ try parseConst
  ignore
  return vs


parseCD :: Parser [Mode]
parseCD = do
  s <- string "#complete_dynamics" -- relational dynamics
  ignore
  modes <- many1 $ try parseMode
  return modes

parseMode :: Parser Mode
parseMode = do
  ignore
  string "mode"
  whitespace
  x <- parseInt
  whitespace
  char ':'
  ignore
  string "uav"
  whitespace
  char ':'
  whitespace
  uavm <- name
  ignore
  string "sensor"
  whitespace
  char ':'
  whitespace
  sm <- name
  ignore
  return Mode { modeId = x, uavMode = uavm, sensorMode = sm }

parseDynamic :: String -> Parser ODE
parseDynamic v = do
  string $ "d/dt[" ++ v ++ "]"
  whitespace
  char '='
  whitespace
  diff <- parseODE
  return diff

parseUAV :: Parser UAVMode
parseUAV = do
  n <- name <?> "uav mode name"
  whitespace
  char ':'
  ignore
  dx <- parseDynamic "x"
  ignore
  db <- parseDynamic "b"
  ignore
  ps <- try parseProg <|> return [] <?> "program"
  ignore
  return UAVMode { modeName = n, xde = dx, bde = db, prog = ps }

parseProg :: Parser [Pred]
parseProg = do
  string "program"
  whitespace
  char '{'
  ps <- many $ try parsePred
  char '}'
  return $ fmap convert ps

parseSensor :: Parser Sensor
parseSensor = do
  ignore
  string "#sensor"
  whitespace
  i <- parseInt
  ignore
  char 'x'
  whitespace
  char '='
  whitespace
  x <- parseNum
  ignore
  ms <- many1 (try parseSMode)
  return Sensor { sId = i, position = x, modes = Map.fromList ms }

parseSMode :: Parser (String, ODE)
parseSMode = do
  n <- name
  whitespace
  char ':'
  ignore
  string "d/dt[q]"
  whitespace
  char '='
  whitespace
  form <- parseODE
  return (n, form)


parseODE :: Parser ODE
parseODE = buildExpressionParser (exprTable EUOp EBin) parseLit <?> "ODE"

parseLit :: Parser ODE
parseLit = try (parens parseODE) <|> try pNum <|> pStr
  where
    pNum = do
      v <- parseNum
      return $ ERealLit v
    pStr = do
      s <- name
      whitespace
      return $ EStrLit s

-- Expression table
exprTable mkUnary mkBinary = [
  [unary Neg],
  [unary Sin, unary Cos, unary Tan],
  [binary Pow AssocNone],
  [binary Times AssocLeft, binary Div AssocLeft],
  [binary Plus AssocLeft, binary Minus AssocLeft],
  [binary Eq AssocNone, binary Leq AssocNone, binary Lt AssocNone, binary Geq AssocNone, binary Gt AssocNone]]
  where
    unary op = Prefix (Token.reservedOp lexer (unOpTokens Map.! op) >> return (mkUnary op))
    binary op = Infix (Token.reservedOp lexer (binOpTokens Map.! op) >> return (mkBinary op))

-- Expr tokens
unOpTokens :: Map UnOp String
unOpTokens = Map.fromList [ (Neg, "-")
                      , (Sin, "sin")
                      , (Cos, "cos")
                      , (Tan, "tan")
                      ]

binOpTokens :: Map BinOp String
binOpTokens = Map.fromList [ (Times, "*")
                       , (Plus,      "+")
                       , (Minus,     "-")
                       , (Div,       "/")
                       , (Pow,       "^")
                       , (Eq,        "==")
                       , (Lt,        "<")
                       , (Leq,       "<=")
                       , (Gt,        ">")
                       , (Geq,       ">=")
                       ]


-- Predicate parsers:
-- TODO: typecheck the predicates? it's possible to have real-valued
--   preds, which are meaningless in an And for example

parsePred :: Parser Pred
parsePred = do
  whitespace
  p <- chainl1 parseTerm parsePEx
  whitespace
  return p

-- Parser for predicate expressions (and, or, etc)
parsePEx :: Parser (Pred -> Pred -> Pred)
parsePEx = do
  onelineWS
  s <- string "=>" <|> string "&&" <|> string "||"
  onelineWS
  case s of
    "=>" -> return Impl
    "&&" -> return BAnd
    "||" -> return BOr

-- Parser for predicate terminals
parseTerm :: Parser Pred
parseTerm = try parseParens <|> try parseNot <|> try parsePLit <|> parseExpr <?> "predicate terminal"


parseExpr :: Parser Pred
parseExpr = do
  e <- parseODE <?> "Predicate expression"
  return $ Expr e

parseParens :: Parser Pred
parseParens = do
  onelineWS
  char '('
  onelineWS
  p <- parsePred
  onelineWS
  char ')'
  return p

parsePLit :: Parser Pred
parsePLit = do
  onelineWS
  s <- string "True" <|> string "False"
  onelineWS
  case s of
    "True" -> return $ Lit True
    "False" -> return $ Lit False

parseNot :: Parser Pred
parseNot = do
  onelineWS
  char '!'
  onelineWS
  p <- parseTerm
  return $ Not p
