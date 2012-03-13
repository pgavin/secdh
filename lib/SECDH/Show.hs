module SECDH.Show where

import Language.Slambda.Types
import Language.Slambda.Util
import Language.Slambda.Show

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as Foldable

import SECDH.Types

showNL :: ShowS
showNL = showChar '\n'

showError :: String -> ShowS
showError str = showString "error" . showBetween lparen (showString str) rparen

showIOAction :: IOAction -> ShowS
showIOAction (ReturnIO a) = showString "(%ioreturn " . showAtom a . showChar ')'
showIOAction (BindIO io a) = showString "(%iobind " . showIOAction io . showChar ' ' . showAtom a . showChar ')'
showIOAction ReadIO = showString "%ioread"
showIOAction (WriteIO c) = showString "(%iowrite '" . showChar c . showString "')"

ioActionToString :: IOAction -> String
ioActionToString = flip showIOAction ""

showAtom :: Atom -> ShowS
showAtom (ErrorA str)             = showError str
showAtom (ConstA k)               = showConst k
showAtom (PrimA p [])             = showPrim p
showAtom (PrimA p xs)             = showChar '(' . showPrim p . showChar ' ' .
                                    foldr (.) id (intersperse (showChar ' ') (map showAtom xs)) .
                                    showChar ')'
showAtom (IOActionA a)            = showIOAction a
showAtom (ClosureA e a i t)       = showBetween lparen (showTerm (AbsT a i t)) rparen . showChar '[' . showEnv e . showChar ']'

atomToString :: Atom -> String
atomToString = flip showAtom ""

showValue :: Value -> ShowS
showValue (AtomV a)    = showAtom a
showValue (PointerV n) = showChar '@' . shows n

showListSepStr :: String -> (a -> ShowS) -> [a] -> ShowS
showListSepStr sep f = foldr (.) id . intersperse (showString sep) . map f

showStack :: Stack -> ShowS
showStack =
  showListSepStr ", " showValue

showEnv :: Env -> ShowS
showEnv =
  showListSepStr "; " showEnvEntry . Map.assocs
  where showEnvEntry (i,n) =
          showVar i . showSpace . showString defineStr . showSpace . showChar '@' . shows n

showInstr :: Instr -> ShowS
showInstr (TermI t)   = showTerm t
showInstr (ApI False) = showString "AP"
showInstr (ApI True)  = showString "!AP"
showInstr (UpdateI n) = showString "UPD@" . shows n
showInstr IOBindI     = showString "IOBIND"

showControl :: Control -> ShowS
showControl =
  showListSepStr ", " showInstr

showObject :: Object -> ShowS
showObject (AtomOb str)  = showAtom str
showObject (SuspOb e t)  = showChar lbracket . (showEnv  e) . showSpace . showChar lambdaSep . showSpace . showTerm t . showChar rbracket
showObject UpdatingOb    = showString "UPD"
showObject (IndirOb n)   = showChar '@' . shows n

showHeap :: ShowS -> Heap -> ShowS
showHeap sep h =
  foldr (.) id $ intersperse sep $
    map (uncurry showHeapEntry) (zip [0..] (Foldable.toList h))
  where showHeapEntry n o =
          showChar '@' . shows n . showChar ':' . showObject o

showDump :: Dump -> ShowS
showDump = 
  showListSepStr ", " showDumpEntry 
  where showDumpEntry (s, e, c) =
          showBetween lparen 
                      (showBetween lparen (showStack s) rparen . showString ", " . 
                       showBetween lparen (showEnv e) rparen . showString ", " .
                       showBetween lparen (showControl c) rparen)
                      rparen

secdhToString :: SECDH -> String
secdhToString = flip showSECDH ""

showSECDH :: SECDH -> ShowS
showSECDH (SECDH s e c d h) =
  showString "Stack:   " . showStack s . showNL .
  showString "Env:     " . showEnv e . showNL .
  showString "Control: " . showControl c . showNL .
  showString "Dump:    " . showDump d . showNL .
  showString "Heap:" . showNL . showSpace . showSpace . showHeap (showNL . showSpace . showSpace) h
