module Language.Slambda.Read
       ( parseTerm
       , readTerm
       , parseProgram
       , readProgram
       ) where

import Language.Slambda.Types
import Language.Slambda.Util

import Control.Monad (liftM, liftM2, when)
import Data.Char
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Text.ParserCombinators.ReadP

parseProgram :: String -> Maybe Program
parseProgram str =
  case readP_to_S (do p <- program; eof; return p) str of
    [(p, "")] -> Just p
    []        -> Nothing
    parses    -> error $ foldr (.) id (showString "multiple parses:\n" : intersperse (showChar '\n') (map shows parses)) ""

readProgram :: ReadS Program
readProgram = readP_to_S program

parseTerm :: String -> Maybe Term
parseTerm str =
  case readP_to_S (do t <- term; eof; return t) str of
    [(t, "")] -> Just t
    []        -> Nothing
    parses    -> error $ "multiple parses: " ++ show parses

readTerm :: ReadS Term
readTerm = readP_to_S term

spaces :: ReadP String
spaces = munch1 isSpace

specialChars :: [Char]
specialChars =
  [ lambda
  , primTag
  , strictTag
  , lambdaSep
  , lparen
  , rparen
  , lbracket
  , rbracket
  , defSep
  , commentStart
  ]

isVarInitChar, isVarRestChar :: Char -> Bool
isVarInitChar c = not (isDigit c) && isVarRestChar c && not (elem c [quote, bottom])
isVarRestChar c = not (isSpace c) && not (elem c specialChars)

var :: ReadP Var
var = do
  first <- satisfy isVarInitChar
  rest  <- munch isVarRestChar
  return $ Var (first:rest)

integer :: ReadP Integer
integer = do
  ds <- munch1 isDigit
  case reads ds of
    [(n, "")] -> return n
    []        -> pfail
    _         -> error "multiple parses for integer"

quotedChar :: ReadP Char
quotedChar = do
  char quote
  c <- do
    c <- get
    case c of
      '\\' -> do
        c <- get
        case c of
          'n'  -> return '\n'
          't'  -> return '\t'
          '\'' -> return '\''
          _    -> pfail
      _    -> return c
  char quote
  return c

skipSC :: ReadP () -- spaces and comments
skipSC = do
  do s <- look
     skip s
  where skip (c:s) | isSpace c         = do _ <- get; skip s
                   | c == commentStart = do _ <- get; skipComment s
        skip _                         = do return ()
        skipComment ('\n':s) = do _ <- get; skip s
        skipComment (_:s)    = do _ <- get; skipComment s
        skipComment []       = do return ()

unitC :: ReadP Const
unitC = do
  char lparen
  skipSC
  char rparen
  return UnitC

bottomC :: ReadP Const
bottomC = do
  char bottom
  return BottomC

integerC :: ReadP Const
integerC =
  liftM IntegerC integer

charC :: ReadP Const
charC =
  liftM CharC quotedChar

constT :: ReadP Term
constT =
  liftM ConstT $ choice [ bottomC
                        , unitC
                        , integerC
                        , charC
                        ]

varT :: ReadP Term
varT = do
  liftM VarT var

primT :: ReadP Term
primT = do
  char primTag
  name <- munch1 isVarRestChar
  case Map.lookup name primsByName of
    Just p  -> return $ PrimT p
    Nothing -> pfail

absT :: ReadP Term
absT = do
  char lambda
  skipSC
  
  vs <- absVars
  
  skipSC
  char lambdaSep
  
  skipSC
  t <- term
  
  return $ foldr (\(s, v) t -> AbsT s v t) t vs
  
  where absVars = do
          sv <- absVar
          vs <- absVars'
          return (sv:vs)
        absVar = do
          s <- option False (char strictTag >> skipSC >> return True)
          v <- var
          return (s, v)
        absVars' = (spaces >> liftM2 (:) absVar absVars') <++ return []

letRecT :: ReadP Term
letRecT = do
  between (char lbracket)
          (char rbracket)

          (do skipSC
              
              ds <- definitions
  
              skipSC
              char lambdaSep
              skipSC
  
              t <- term
              
              skipSC
              return (LetRecT ds t))

nonAppT = do
  choice [ constT
         , varT
         , primT
         , absT
         , letRecT
         , between (char lparen >> skipSC)
                   (skipSC >> char rparen)
                   term
         ]

term = do
  skipSC
  t <- nonAppT
  ts <- term'
  return $ foldl1 AppT (t:ts)
  where term' = (spaces >> liftM2 (:) nonAppT term') <++ return []

definition :: ReadP Def
definition = do
  skipSC
  v <- var
  skipSC
  string defineStr
  t <- term
  skipSC
  return (v, t)

definitions :: ReadP [Def]
definitions = do
  defs <- between emptyDefs
                  emptyDefs
                  (sepBy definition (char defSep >> emptyDefs))
  when (not (null defs)) $ do
    let vars = sort (map fst defs)
        hasDup v [] = False
        hasDup v (v':vs) = v == v' || hasDup v' vs
    when (hasDup (head vars) (tail vars)) pfail
  return defs
  where emptyDefs = do
          skipSpaces
          optional (char defSep >> emptyDefs)

program :: ReadP Program
program = do
  skipSC
  ds <- definitions
  skipSC
  return ds
