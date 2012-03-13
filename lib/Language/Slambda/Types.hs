module Language.Slambda.Types where

import Data.Map (Map)
import qualified Data.Map as Map

newtype Var = Var { varName :: String }
              deriving (Eq, Ord, Show, Read)

type Arity = Int

data Prim = IOReturnP
          | IOBindP
          | IOReadP
          | IOWriteP
          | UnitPP
          | IntegerPP
          | LambdaPP
          | NegP
          | SuccP
          | PredP
          | Mul2P
          | Div2P
          | ZeroPP
          | PosPP
          | EvenPP
          | OddPP
          | AddP
          | SubP
          | MulP
          | DivP
          | ModP
          | EqPP
          | ChrP
          | OrdP
          deriving (Eq, Ord, Show, Read, Enum, Bounded)

data Const = BottomC
           | UnitC
           | IntegerC { constInteger :: !Integer }
           | CharC    { constChar    :: !Char    }
           deriving (Eq, Ord, Show, Read)

type Strictness = Bool

type Def      = (Var, Term)
type Program  = [Def]

data Term = VarT { termVar :: Var }
          | ConstT { termConst :: Const }
          | PrimT { termPrim :: Prim }
          | AbsT { termAbsStrict :: !Strictness, termAbsVar :: Var, termAbsSubterm :: Term }
          | AppT { termAppFunc :: Term, termAppArg :: Term }
          | LetRecT { termLetRecDefs :: [Def], termLetRecSubterm :: Term }
            deriving (Eq, Show, Read)
