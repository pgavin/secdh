module Language.Slambda.Util where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Language.Slambda.Types

lambda = '\\'
lambdaSep = '.'
bottom = '_'
primTag = '%'
strictTag = '!'
lparen = '('
rparen = ')'
defSep = ';'
commentStart = '#'
lbracket = '['
rbracket = ']'
quote = '\''

unitStr, defineStr :: String
unitStr = "()"
defineStr = ":="

mainProgramName :: String
mainProgramName = "main"

primName :: Prim -> String
primName IOReturnP = "ioreturn"
primName IOBindP   = "iobind"
primName IOReadP   = "ioread"
primName IOWriteP  = "iowrite"
primName UnitPP    = "unit?"
primName IntegerPP = "integer?"
primName LambdaPP  = "lambda?"
primName NegP      = "neg"
primName SuccP     = "succ"
primName PredP     = "pred"
primName Mul2P     = "mul2"
primName Div2P     = "div2"
primName ZeroPP    = "zero?"
primName PosPP     = "pos?"
primName EvenPP    = "even?"
primName OddPP     = "odd?"
primName AddP      = "add"
primName SubP      = "sub"
primName MulP      = "mul"
primName DivP      = "div"
primName ModP      = "mod"
primName EqPP      = "eq?"
primName ChrP      = "chr"
primName OrdP      = "ord"

primsByName :: Map String Prim
primsByName =
  Map.fromList [ (primName p, p) | p <- [minBound..maxBound] ]

xV, yV :: Var
xV = Var "x"
yV = Var "y"

trueT :: Term
trueT = AbsT False xV (AbsT False yV (VarT xV))

falseT :: Term
falseT = AbsT False xV (AbsT False yV (VarT yV))

freeVars :: Term -> Set Var
freeVars (VarT v)       = Set.singleton v
freeVars (ConstT _)     = Set.empty
freeVars (PrimT _)      = Set.empty
freeVars (AbsT _ v t)   = Set.delete v (freeVars t)
freeVars (AppT f x)     = Set.union (freeVars f) (freeVars x)
freeVars (LetRecT ds t) =
  let (vs, ts) = unzip ds
  in Set.difference (foldl Set.union (freeVars t) (map freeVars ts)) (Set.fromList vs)

showBetween :: Char -> ShowS -> Char -> ShowS
showBetween l s r = showChar l . s . showChar r

showSpace :: ShowS
showSpace = showChar ' '

showStrictness :: Bool -> ShowS
showStrictness s | s         = showChar strictTag
                 | otherwise = id

