{-# LANGUAGE BangPatterns, PatternGuards #-}

module SECDH.Eval 
       ( secdhEval
       , secdhInit
       , secdhInitProgram
       , secdhFinish
       , secdhEvalStats
       , secdhFinishStats
       , secdhIter
       , Rule (..)
       ) where

--import Debug.Trace

import Language.Slambda.Types
import Language.Slambda.Show
import Language.Slambda.Util

import SECDH.Types
import SECDH.Show

import Control.Monad
import Data.Bits (shiftL, shiftR)
import Data.Char
import Data.List
import Data.Monoid
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq

secdhStats :: SECDH -> Rule -> SECDHStats
secdhStats (SECDH s e c d h) r =
  SECDHStats
  { secdhStatsIters       = 1
  , secdhStatsMaxStack    = length s
  , secdhStatsMaxEnv      = Map.size e
  , secdhStatsMaxControl  = length c
  , secdhStatsMaxDump     = length d
  , secdhStatsMaxHeap     = Seq.length h
  , secdhStatsMaxRetained = 0
  , secdhStatsGCs         = 0
  , secdhStatsRuleExecs   = Map.singleton r 1
  }

emptyEnv :: Env
emptyEnv = Map.empty
emptyHeap :: Heap
emptyHeap = Seq.empty

loopA :: Atom
loopA = ErrorA "loop"

termToClosure :: Term -> Atom
termToClosure (AbsT s i t) = ClosureA emptyEnv s i t
termToClosure t = error $ "cannot make closure from non-abstraction term: " ++ termToString t

trueA, falseA :: Atom
trueA  = termToClosure trueT
falseA = termToClosure falseT

pruneEnv :: Term -> Env -> Env
pruneEnv t =
  let vs = freeVars t
  in Map.filterWithKey (\v n -> Set.member v vs)

mkClosure :: Env -> Strictness -> Var -> Term -> Atom
mkClosure e s i t =
  ClosureA (pruneEnv t e) s i t

mkObject :: Env -> Term -> Object
mkObject _ (ConstT k)   = AtomOb (ConstA k)
mkObject _ (PrimT p)    = AtomOb (primToAtom p)
mkObject e (AbsT s i t) = AtomOb (mkClosure e s i t)
mkObject e t            = SuspOb (pruneEnv t e) t

primToAtom :: Prim -> Atom
primToAtom IOReadP = IOActionA ReadIO
primToAtom p       = PrimA p []

primArity :: Prim -> Arity
primArity IOReturnP = 1
primArity IOBindP   = 2
primArity IOReadP   = 0
primArity IOWriteP  = 1
primArity UnitPP    = 1
primArity IntegerPP = 1
primArity LambdaPP  = 1
primArity NegP      = 1
primArity SuccP     = 1
primArity PredP     = 1
primArity Mul2P     = 1
primArity Div2P     = 1
primArity ZeroPP    = 1
primArity PosPP     = 1
primArity EvenPP    = 1
primArity OddPP     = 1
primArity AddP      = 2
primArity SubP      = 2
primArity MulP      = 2
primArity DivP      = 2
primArity ModP      = 2
primArity EqPP      = 2
primArity ChrP      = 1
primArity OrdP      = 1

invalidPrimAppError :: Prim -> [Atom] -> Atom
invalidPrimAppError p xs =
  ErrorA ("invalid application of primitive %" ++ primName p ++ " to arguments " ++
          concat (intersperse ", " (map atomToString xs)))

applyPrim :: Prim -> [Atom] -> Atom

applyPrim p         xs | length xs /= primArity p                  =
  error $ "invalid number of arguments (" ++ show (length xs) ++ ") supplied for primitive " ++ primName p

applyPrim IOReturnP [a]                                            = IOActionA (ReturnIO a)

applyPrim IOBindP   [ErrorA s, _]                                  = ErrorA s
applyPrim IOBindP   [ConstA BottomC, _]                            = ConstA BottomC
applyPrim IOBindP   [IOActionA io, a]                              = IOActionA (BindIO io a)
applyPrim IOBindP   xs                                             = invalidPrimAppError IOBindP xs

-- the remaining primitives are strict in both arguments
applyPrim _         args
  | Just a <- find (\a -> case a of ErrorA _ -> True; _ -> False) args = a
applyPrim _         args
  | Just a <- find (\a -> case a of ConstA BottomC -> True; _ -> False) args = a

applyPrim IOWriteP  [ConstA (CharC ch)]                            = IOActionA (WriteIO ch)

applyPrim UnitPP    [ConstA UnitC]                                 = trueA
applyPrim UnitPP    [_]                                            = falseA

applyPrim IntegerPP [ConstA (IntegerC _)]                          = trueA
applyPrim IntegerPP [_]                                            = falseA

applyPrim LambdaPP  [ClosureA _ _ _ _]                             = trueA
applyPrim LambdaPP  [PrimA p args] | primArity p - length args > 0 = trueA
applyPrim LambdaPP  [_]                                            = falseA

applyPrim NegP      [ConstA (IntegerC x)]                          = ConstA (IntegerC (negate x))

applyPrim SuccP     [ConstA (IntegerC x)]                          = ConstA (IntegerC (succ x))

applyPrim PredP     [ConstA (IntegerC x)]                          = ConstA (IntegerC (pred x))

applyPrim Mul2P     [ConstA (IntegerC x)]                          = ConstA (IntegerC (x * 2))

applyPrim Div2P     [ConstA (IntegerC x)]                          = ConstA (IntegerC (x `div` 2))

applyPrim ZeroPP    [ConstA (IntegerC 0)]                          = trueA
applyPrim ZeroPP    [_]                                            = falseA

applyPrim PosPP     [ConstA (IntegerC n)] | n > 0                  = trueA
applyPrim PosPP     [_]                                            = falseA

applyPrim EvenPP    [ConstA (IntegerC n)] | even n                 = trueA
applyPrim EvenPP    [_]                                            = falseA

applyPrim OddPP     [ConstA (IntegerC n)] | odd n                  = trueA
applyPrim OddPP     [_]                                            = falseA

applyPrim AddP      [ConstA (IntegerC x), ConstA (IntegerC y)]     = ConstA (IntegerC (x + y))
applyPrim SubP      [ConstA (IntegerC x), ConstA (IntegerC y)]     = ConstA (IntegerC (x - y))
applyPrim MulP      [ConstA (IntegerC x), ConstA (IntegerC y)]     = ConstA (IntegerC (x * y))
applyPrim DivP      [ConstA (IntegerC x), ConstA (IntegerC y)]     = ConstA (IntegerC (x `div` y))
applyPrim ModP      [ConstA (IntegerC x), ConstA (IntegerC y)]     = ConstA (IntegerC (x `mod` y))

applyPrim EqPP      [ConstA (IntegerC x), ConstA (IntegerC y)] | x == y = trueA
applyPrim EqPP      [ConstA (CharC x),    ConstA (CharC y)]    | x == y = trueA
applyPrim EqPP      [ConstA UnitC,        ConstA UnitC]                 = trueA
applyPrim EqPP      [_, _]                                              = falseA

applyPrim ChrP      [ConstA (IntegerC n)]                          = ConstA (CharC (chr (fromInteger n)))
applyPrim OrdP      [ConstA (CharC c)]                             = ConstA (IntegerC (toInteger (ord c)))

applyPrim p         xs                                             =
  invalidPrimAppError p xs

secdhEval :: MonadSECDHIO m => Program -> m Atom
secdhEval =
  liftM snd . secdhFinish . secdhGC . secdhInitProgram

secdhEvalStats :: MonadSECDHIO m => Program -> m (Atom, SECDHStats)
secdhEvalStats =
  liftM (\(_, r, s) -> (r, s)) . secdhFinishStats . secdhGC . secdhInitProgram

secdhInit :: Env -> Heap -> Term -> SECDH
secdhInit e h t =
  SECDH
  { secdhStack   = []
  , secdhEnv     = e
  , secdhControl = [TermI t]
  , secdhDump    = []
  , secdhHeap    = h
  }

secdhInitProgram :: Program -> SECDH
secdhInitProgram prog =
  secdhInit emptyEnv emptyHeap (LetRecT prog (VarT (Var mainProgramName)))

secdhGCFactor = 4
secdhGCInitLimit = 1024

secdhFinish :: MonadSECDHIO m => SECDH -> m (SECDH, Atom)
secdhFinish = secdhFinish' secdhGCInitLimit
  where secdhFinish' !gcLim !secdh = do
          (secdh', _, mbResult) <- secdhIter secdh
          case mbResult of
            Just r ->
              return (secdh', r)
            Nothing ->
              if Seq.length (secdhHeap secdh') > gcLim
              then let secdh'' = secdhGC secdh'
                       gcLim' = max gcLim (secdhGCFactor * Seq.length (secdhHeap secdh''))
                   in --trace ("Retained: " ++ show (Seq.length (secdhHeap secdh'')) ++ "\nGC Limit: " ++ show gcLim') $
                      secdhFinish' gcLim' secdh''
              else secdhFinish' gcLim secdh'

secdhFinishStats :: MonadSECDHIO m => SECDH -> m (SECDH, Atom, SECDHStats)
secdhFinishStats = secdhFinishStats' mempty secdhGCInitLimit
  where secdhFinishStats' !stats !gcLim secdh = do
          (secdh', rule, mbResult) <- secdhIter secdh
          case mbResult of
            Just r ->
              return (secdh', r, stats)
            Nothing ->
              if Seq.length (secdhHeap secdh') > gcLim
              then let !secdh'' = secdhGC secdh'
                       !gcLim'  = max gcLim (secdhGCFactor * Seq.length (secdhHeap secdh''))
                       !stats'  = stats { secdhStatsGCs = succ (secdhStatsGCs stats)
                                        , secdhStatsMaxRetained = max (secdhStatsMaxRetained stats) (Seq.length (secdhHeap secdh'')) }
                   in secdhFinishStats' (mappend stats' (secdhStats secdh rule)) gcLim' secdh''
              else secdhFinishStats' (mappend stats (secdhStats secdh rule)) gcLim secdh'

secdhApplyNonFunctionError :: String -> Atom
secdhApplyNonFunctionError s =
  ErrorA (s ++ " is not a function, but treated as one")

invalidSECDHState :: SECDH -> a
invalidSECDHState secdh =
  error $ "invalid secdh state:\n" ++ secdhToString secdh

secdhIter :: MonadSECDHIO m => SECDH -> m (SECDH, Rule, Maybe Atom)
-- Perform IO
secdhIter secdh@(SECDH [AtomV (IOActionA io)] _ [] [] h) =
  case io of
    ReturnIO a ->
      return ( secdh
             , Rule 1
             , Just a )
    BindIO io a ->
      return ( SECDH [AtomV (IOActionA io),AtomV a] emptyEnv [IOBindI] [] h
             , Rule 2
             , Nothing )
    ReadIO -> do
      mbc <- secdhRead
      return ( SECDH [AtomV (ConstA (maybe UnitC CharC mbc))] emptyEnv [] [] h
             , Rule 3
             , Nothing )
    WriteIO ch -> do
      secdhWrite ch
      return ( SECDH [AtomV (ConstA UnitC)] emptyEnv [] [] h
             , Rule 4
             , Nothing )
-- Termination condition.
secdhIter secdh@(SECDH [v@(AtomV a)] _ [] [] _) =
  return ( secdh
         , Rule 5
         , Just a )
-- Pop off the dump stack when a sub-computation is completed.
secdhIter (SECDH [v] _ [] ((s', e', c'):d') h) =
  return ( SECDH (v:s') e' c' d' h
         , Rule 6
         , Nothing )
-- If a pointer is all that's left, dereference it and, if necessary,
-- set up an update and enter a suspension.
secdhIter (SECDH [PointerV n] e [] [] h) | n < Seq.length h =
  case Seq.index h n of
    AtomOb a ->
      return ( SECDH [AtomV a] e [] [] h
             , Rule 7
             , Nothing )
    SuspOb e' t ->
      return ( SECDH [] e' [TermI t] [([],e,[UpdateI n])] (Seq.update n UpdatingOb h)
             , Rule 8
             , Nothing )
    IndirOb n' ->
      return ( SECDH [PointerV n'] e [] [] h
             , Rule 9
             , Nothing )
    UpdatingOb ->
      return ( SECDH [AtomV loopA] e [] [] h
             , Rule 10
             , Nothing )
secdhIter (SECDH (PointerV n:s) e (IOBindI:c) [] h) =
  case Seq.index h n of
    AtomOb a ->
      return ( SECDH (AtomV a:s) e (IOBindI:c) [] h
             , Rule 11
             , Nothing )
    SuspOb e' t ->
      return ( SECDH [] e' [TermI t] [(s,e,UpdateI n:IOBindI:c)] (Seq.update n UpdatingOb h)
             , Rule 12
             , Nothing )
    IndirOb n' ->
      return ( SECDH (PointerV n':s) e (IOBindI:c) [] h
             , Rule 13
             , Nothing )
    UpdatingOb ->
      return ( SECDH (AtomV loopA:s) e (IOBindI:c) [] h
             , Rule 14
             , Nothing )
secdhIter (SECDH (AtomV (IOActionA io):s) e (IOBindI:c) [] h) =
  case io of
    ReturnIO a ->
      return ( SECDH (AtomV a:s) e (ApI True:c) [] h
             , Rule 15
             , Nothing )
    BindIO io a ->
      return ( SECDH (AtomV (IOActionA io):AtomV a:s) e (IOBindI:IOBindI:c) [] h
             , Rule 16
             , Nothing )
    ReadIO -> do
      mbc <- secdhRead
      return ( SECDH (AtomV (ConstA (maybe UnitC CharC mbc)):s) e (ApI True:c) [] h
             , Rule 17
             , Nothing )
    WriteIO ch -> do
      secdhWrite ch
      return ( SECDH (AtomV (ConstA UnitC):s) e (ApI True:c) [] h
             , Rule 18
             , Nothing )
secdhIter (SECDH (AtomV (ErrorA r):s) e (IOBindI:c) [] h) =
  return ( SECDH (AtomV (ErrorA r):s) e (ApI True:c) [] h
         , Rule 19
         , Nothing )
secdhIter (SECDH (AtomV (ConstA BottomC):s) e (IOBindI:c) [] h) =
  return ( SECDH (AtomV (ConstA BottomC):s) e (ApI True:c) [] h
         , Rule 20
         , Nothing )
secdhIter (SECDH (AtomV a:s) e (IOBindI:c) [] h) =
  return ( SECDH (AtomV (ErrorA ("trying to leave io monad; result was: " ++ atomToString a)):s) e (ApI True:c) [] h
         , Rule 21
         , Nothing )
-- Handle tail calls.
secdhIter (SECDH [f,x] e [ApI False] ((s', e', c'):d) h) =
  return ( SECDH (f:x:s') e' (ApI False:c') d h
         , Rule 22
         , Nothing )
-- If the next instruction is UpdateI, and we have an atom, then
-- update the heap and pop the instruction
secdhIter (SECDH s@(AtomV a:_) e (UpdateI n:c) d h) =
  return ( SECDH s e c d (Seq.update n (AtomOb a) h)
         , Rule 23
         , Nothing )
-- If the next instruction is UpdateI, and we have a pointer:
-- If the pointer is to an atom, just replace the pointer with the atom
-- (the next iteration will do the update).
-- If the pointer is to a suspension, then replace the suspension being pointed to by an indirection
-- to the block being updated, and enter the suspension (this prevents a chain of updates from piling up on the C stack).
-- If the pointer is already being updated, we're in a loop.
secdhIter (SECDH (PointerV n:s) e c@(UpdateI u:c') d h) | n < Seq.length h =
  case Seq.index h n of
    AtomOb a ->
      return ( SECDH (AtomV a:s) e c d h
             , Rule 24
             , Nothing )
    SuspOb e' t ->
      return ( SECDH [] e' [TermI t] ((s,e,c):d) (Seq.update n (IndirOb u) h)
             , Rule 25
             , Nothing )
    IndirOb r ->
      return ( SECDH (PointerV r:s) e c d (Seq.update n (IndirOb u) h)
             , Rule 26
             , Nothing )
    UpdatingOb ->
      return ( SECDH (AtomV loopA:s) e c d h
             , Rule 27
             , Nothing )
-- If the next instruction is TermI, move the term onto the stack,
-- making abstractions into closures, and pushing ApI instructions for
-- applications.
-- LetRec creates a suspension in the updated environment.
secdhIter (SECDH s e (TermI t:c) d h)
  | VarT i <- t = do
    let v = case Map.lookup i e of
              Just n  -> PointerV n
              Nothing -> AtomV (ErrorA ("undefined variable: " ++ varName i))
    return ( SECDH (v:s) e c d h
           , Rule 28
           , Nothing )
  | ConstT k <- t =
    return ( SECDH (AtomV (ConstA k):s) e c d h
           , Rule 29
           , Nothing )
  | PrimT p <- t =
    return ( SECDH (AtomV (primToAtom p):s) e c d h
           , Rule 30
           , Nothing )
  | AbsT a i t' <- t = do
    return ( SECDH (AtomV (mkClosure e a i t'):s) e c d h
           , Rule 31
           , Nothing )
  | AppT f x <- t =
    return ( SECDH (PointerV (Seq.length h):s) e (TermI f:ApI False:c) d (h |> mkObject e x)
           , Rule 32
           , Nothing )
  | LetRecT ds t' <- t = do
    let e' = foldl (flip (uncurry Map.insert)) e (zip (map fst ds) (enumFrom (Seq.length h)))
        h' = foldl (|>) h (map (mkObject e' . snd) ds)
    return ( SECDH (PointerV (Seq.length h'):s) e c d (h' |> mkObject e' t')
           , Rule 33
           , Nothing )
-- Apply a function.  If the function is a non-strict closure, just
-- make an updated environment and heap for the argument, and enter
-- the function after pushing the current state on the dump.  The
-- function is strict, swap the top 2 stack positions, and replace the
-- (ApI False) instruction with an (ApI True) instruction.  If the
-- function is a pointer, deference the pointer and enter the
-- suspension if necessary.
secdhIter (SECDH (f:x:s) e (ApI False:c) d h)
  | AtomV (ErrorA str) <- f =
    return ( SECDH (f:s) e c d h
           , Rule 34
           , Nothing )
  | AtomV (ConstA BottomC) <- f =
    return ( SECDH (AtomV (ConstA BottomC):s) e c d h
           , Rule 35
           , Nothing )
  | AtomV (ConstA k) <- f =
    return ( SECDH (AtomV (secdhApplyNonFunctionError (constToString k)):s) e c d h
           , Rule 36
           , Nothing )
  | AtomV (PrimA p []) <- f, primArity p < 1 =
    return ( SECDH (AtomV (secdhApplyNonFunctionError ('%':primName p)):s) e c d h
           , Rule 37
           , Nothing )
  | AtomV (IOActionA io) <- f =
    return ( SECDH (AtomV (secdhApplyNonFunctionError (ioActionToString io)):s) e c d h
           , Rule 38
           , Nothing )
  | AtomV (PrimA p _) <- f, primArity p >= 1 =
    return ( SECDH (x:f:s) e (ApI True:c) d h
           , Rule 39
           , Nothing )
  | AtomV (ClosureA e False i t) <- f = do
    let (e', h') =
          case x of
            AtomV xA   -> (Map.insert i (Seq.length h) e, h |> AtomOb xA)
            PointerV n -> (Map.insert i n e, h)
    return ( SECDH [] e' [TermI t] ((s,e,c):d) h'
           , Rule 40
           , Nothing )
  | AtomV (ClosureA e True i t) <- f =
    return ( SECDH (x:f:s) e (ApI True:c) d h
           , Rule 41
           , Nothing )
  | PointerV n <- f, n < Seq.length h =
    case Seq.index h n of
      AtomOb f' ->
        return ( SECDH (AtomV f':x:s) e (ApI False:c) d h
               , Rule 42
               , Nothing )
      SuspOb e' t' ->
        return ( SECDH [] e' [TermI t'] ((x:s,e,UpdateI n:ApI False:c):d) h
               , Rule 43
               , Nothing )
      IndirOb n' ->
        return ( SECDH (PointerV n':x:s) e (UpdateI n:ApI False:c) d h
               , Rule 44
               , Nothing )
      UpdatingOb ->
        return ( SECDH (AtomV loopA:s) e c d h
               , Rule 45
               , Nothing )
-- Apply a strict function. If the argument is a pointer, deference it
-- and, if necessary, set up the update and enter the suspension.
secdhIter (SECDH (x:f:s) e (ApI True:c) d h)
  | PointerV n <- x, n < Seq.length h =
    case Seq.index h n of
      AtomOb xA ->
        return ( SECDH (AtomV xA:f:s) e (ApI True:c) d h
               , Rule 46
               , Nothing )
      SuspOb e' t' ->
        return ( SECDH [] e' [TermI t'] ((f:s,e,UpdateI n:ApI True:c):d) h
               , Rule 47
               , Nothing )
      IndirOb n' ->
        return ( SECDH (PointerV n':f:s) e (UpdateI n:ApI True:c) d h
               , Rule 48
               , Nothing )
      UpdatingOb ->
        return ( SECDH (AtomV loopA:s) e c d h
               , Rule 49
               , Nothing )
  | AtomV (ErrorA str) <- x =
    return ( SECDH (x:s) e c d h
           , Rule 50
           , Nothing )
  | AtomV xA <- x, AtomV (PrimA p args) <- f =
    if 1 + length args == primArity p
    then return ( SECDH (AtomV (applyPrim p (reverse (xA:args))):s) e c d h
                , Rule 51
                , Nothing )
    else return ( SECDH (AtomV (PrimA p (xA:args)):s) e c d h
                , Rule 52
                , Nothing )
  | AtomV xA <- x, AtomV (ClosureA e _ i t) <- f =
    return ( SECDH [] (Map.insert i (Seq.length h) e) [TermI t] ((s,e,c):d) (h |> AtomOb xA)
           , Rule 53
           , Nothing )
-- Should never, ever, ever, ever get here.
-- Ever.
secdhIter secdh =
  invalidSECDHState secdh

secdhGC :: SECDH -> SECDH
secdhGC secdh@(SECDH s e c d h) =
  let ns = sRefs s ++ eRefs e ++ cRefs c ++ dRefs d
      (m, h') = copy ns h
  in SECDH (remaps m s) (remape m e) (remapc m c) (remapd m d) (remaph m h')
  
  where atomRefs :: Atom -> [Addr]
        atomRefs (PrimA _ args)     = args >>= atomRefs
        atomRefs (ClosureA e _ _ _) = eRefs e
        atomRefs (IOActionA io)     = ioRefs io
        atomRefs _                  = mzero
        
        ioRefs (ReturnIO a)  = atomRefs a
        ioRefs (BindIO io a) = ioRefs io `mplus` atomRefs a
        ioRefs _             = mzero
        
        sRefs :: Stack -> [Addr]
        sRefs s = do
          v <- s
          case v of
            AtomV a    -> atomRefs a
            PointerV n -> return n
        eRefs :: Env -> [Addr]
        eRefs e =
          Map.elems e
        cRefs :: Control -> [Addr]
        cRefs c = do
          i <- c
          case i of
            UpdateI n -> return n
            _         -> mzero
        dRefs :: Dump -> [Addr]
        dRefs d = do
          (s,e,c) <- d
          sRefs s `mplus` eRefs e `mplus` cRefs c
        
        copy :: [Addr] -> Heap -> (Map Addr Addr, Heap)
        copy =
          let copy' :: Map Addr Addr -> Heap -> [Addr] -> Heap -> (Map Addr Addr, Heap)
              copy' m hn nos ho =
                case nos of
                  [] -> (m, hn)
                  no:nos' ->
                    case Map.lookup no m of
                      Just _ ->
                        copy' m hn nos' ho
                      Nothing ->
                        let nn = Seq.length hn
                            o = Seq.index h no
                            m' = Map.insert no nn m
                            hn' = hn |> o
                        in case Seq.index ho no of
                             SuspOb e _ ->
                               copy' m' hn' (Map.elems e ++ nos') ho
                             IndirOb po ->
                               case Map.lookup po m of
                                 Just pn ->
                                   copy' (Map.insert no pn m) hn nos' ho
                                 Nothing ->
                                   copy' m hn (po:no:nos') ho
                             AtomOb a ->
                               copy' m' hn' (atomRefs a ++ nos') ho
                             o ->
                               copy' m' hn' nos' ho
          in copy' Map.empty Seq.empty
        
        remapio :: Map Addr Addr -> IOAction -> IOAction
        remapio m (ReturnIO a)  = ReturnIO (remapAtom m a)
        remapio m (BindIO io a) = BindIO (remapio m io) (remapAtom m a)
        remapio _ io            = io
        
        remapAtom :: Map Addr Addr -> Atom -> Atom
        remapAtom m (PrimA p args)     = PrimA p (map (remapAtom m) args)
        remapAtom m (IOActionA io)     = IOActionA (remapio m io)
        remapAtom m (ClosureA e s i t) = ClosureA (remape m e) s i t
        remapAtom _ a                  = a
        
        remaps :: Map Addr Addr -> Stack -> Stack
        remaps m = map $ \v ->
          case v of 
            AtomV a ->
              AtomV (remapAtom m a)
            PointerV n -> 
              PointerV (m ! n)
        
        remape :: Map Addr Addr -> Env -> Env
        remape m = Map.map (m!)
        
        remapc :: Map Addr Addr -> Control -> Control
        remapc m = map $ \i -> 
          case i of
            UpdateI n -> UpdateI (m ! n)
            _         -> i
        
        remapd :: Map Addr Addr -> Dump -> Dump
        remapd m = map $ \(s, e, c) ->
          (remaps m s, remape m e, remapc m c)
        
        remaph :: Map Addr Addr -> Heap -> Heap
        remaph m = fmap $ \o ->
          case o of
            AtomOb a -> AtomOb (remapAtom m a)
            SuspOb e t -> SuspOb (remape m e) t
            IndirOb p -> IndirOb (m ! p)
            _ -> o
