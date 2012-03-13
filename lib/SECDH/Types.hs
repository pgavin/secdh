{-# LANGUAGE BangPatterns #-}
module SECDH.Types where

import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import System.IO

import Language.Slambda.Types

data Instr = TermI { instrTerm :: Term }
           | ApI Bool -- indicates that argument is at top of stack, function is just below it, 
                      -- *and* that the function is strict in its argument
           | UpdateI Addr -- indicates that the atom at the top of the
                          -- stack should be written to the given
                          -- address
           | IOBindI -- perform whatever io action is on the top of the stack and apply the function underneath it to the result
           deriving (Show, Read)

type Addr = Int

data IOAction = ReturnIO !Atom
              | BindIO !IOAction !Atom
              | WriteIO  !Char
              | ReadIO
                deriving (Show, Read)

data Atom = ErrorA String
          | ConstA !Const
          | PrimA !Prim [Atom]
          | IOActionA !IOAction
          | ClosureA Env !Strictness Var Term
          deriving (Show, Read)

data Value = AtomV !Atom
           | PointerV !Addr
           deriving (Show, Read)

data Object = AtomOb !Atom
            | SuspOb Env Term
            | IndirOb !Addr -- Indirection to another object
            | UpdatingOb -- Object is being updated
            deriving (Show, Read)

type Stack   = [Value]
type Env     = Map Var Addr
type Control = [Instr]
type Dump    = [(Stack, Env, Control)]
type Heap    = Seq Object

data SECDH = SECDH
             { secdhStack   :: !Stack
             , secdhEnv     :: !Env
             , secdhControl :: !Control
             , secdhDump    :: !Dump
             , secdhHeap    :: Seq Object
             } deriving (Show, Read)

newtype Rule = Rule { ruleNum :: Int }
               deriving (Eq, Ord, Show, Read)

class Monad m => MonadSECDHIO m where
  secdhRead  :: m (Maybe Char)
  secdhWrite :: Char -> m ()
  secdhWriteErr :: Char -> m ()

instance MonadSECDHIO IO where
  secdhRead = do
    eof <- isEOF
    if not eof
      then fmap Just getChar
      else return Nothing
  secdhWrite = putChar
  secdhWriteErr = hPutChar stderr

data SECDHStats = SECDHStats
                  { secdhStatsIters       :: !Int
                  , secdhStatsMaxStack    :: !Int
                  , secdhStatsMaxEnv      :: !Int
                  , secdhStatsMaxControl  :: !Int
                  , secdhStatsMaxDump     :: !Int
                  , secdhStatsMaxHeap     :: !Int
                  , secdhStatsMaxRetained :: !Int
                  , secdhStatsGCs         :: !Int
                  , secdhStatsRuleExecs   :: !(Map Rule Int)
                  }
instance Monoid SECDHStats where
  mempty =
    SECDHStats
    { secdhStatsIters       = 0
    , secdhStatsMaxStack    = 0
    , secdhStatsMaxEnv      = 0
    , secdhStatsMaxControl  = 0
    , secdhStatsMaxDump     = 0
    , secdhStatsMaxHeap     = 0
    , secdhStatsMaxRetained = 0
    , secdhStatsGCs         = 0
    , secdhStatsRuleExecs   = Map.empty
    }
  mappend s1 s2 =
    SECDHStats
    { secdhStatsIters       = secdhStatsIters s1 + secdhStatsIters s2
    , secdhStatsMaxStack    = max (secdhStatsMaxStack s1)    (secdhStatsMaxStack s2)
    , secdhStatsMaxEnv      = max (secdhStatsMaxEnv s1)      (secdhStatsMaxEnv s2)
    , secdhStatsMaxControl  = max (secdhStatsMaxControl s1)  (secdhStatsMaxControl s2)
    , secdhStatsMaxDump     = max (secdhStatsMaxDump s1)     (secdhStatsMaxDump s2)
    , secdhStatsMaxHeap     = max (secdhStatsMaxHeap s1)     (secdhStatsMaxHeap s2)
    , secdhStatsMaxRetained = max (secdhStatsMaxRetained s1) (secdhStatsMaxRetained s2)
    , secdhStatsGCs         = secdhStatsGCs s1 + secdhStatsGCs s2
    , secdhStatsRuleExecs =
        let f a (r, n) =
              case Map.lookup r a of
                Just n' -> let !n'' = n + n'
                           in Map.insert r n'' a
                Nothing -> Map.insert r n a
        in foldl f (secdhStatsRuleExecs s1) (Map.assocs (secdhStatsRuleExecs s2))
    }
