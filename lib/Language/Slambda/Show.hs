module Language.Slambda.Show
       ( showVar
       , constToString
       , showConst
       , showPrim
       , termToString
       , showTerm
       , defToString
       , showDef
       , programToString
       , showProgram
       ) where

import Data.List

import Language.Slambda.Types
import Language.Slambda.Util

constToString :: Const -> String
constToString = flip showConst ""

showConst :: Const -> ShowS
showConst BottomC      = showChar bottom
showConst UnitC        = showString unitStr
showConst (IntegerC n) = shows n
showConst (CharC '\n') = showString "'\\n'"
showConst (CharC '\t') = showString "'\\t'"
showConst (CharC c)    = showChar '\'' . showChar c . showChar '\''

showPrim :: Prim -> ShowS
showPrim p =
  showChar primTag . showString (primName p)

termToString :: Term -> String
termToString = flip showTerm ""
defToString :: Def -> String
defToString = flip showDef ""
programToString :: Program -> String
programToString = flip (showProgram (showChar '\n')) ""

showVar :: Var -> ShowS
showVar = showString . varName

showDef :: Def -> ShowS
showDef (v, t) =
  showVar v . showSpace . showString defineStr . showSpace . showTerm t

showProgram :: ShowS -> Program -> ShowS
showProgram sep =
  foldr (.) id . map (\d -> showDef d . showChar defSep . sep)

showTerm :: Term -> ShowS
showTerm (VarT v)                = showVar v
showTerm (ConstT k)              = showConst k
showTerm (AbsT s v t)            = showChar lambda . showAbs s v t
showTerm (AppT f@(AbsT _ _ _) x) = showBetween lparen (showTerm f) rparen . showSpace . showTerm' x
showTerm (AppT f x)              = showTerm f . showSpace . showTerm' x
showTerm (PrimT p)               = showPrim p
showTerm (LetRecT ds t)          = showBetween lbracket 
                                                   (foldr (.) id (intersperse (showString "; ") (map showDef ds)) . 
                                                    showSpace . showChar lambdaSep . showSpace . showTerm t) 
                                                   rbracket


showTerm' :: Term -> ShowS
showTerm' t@(AbsT _ _ _) = showBetween lparen (showTerm t) rparen
showTerm' t@(AppT _ _)   = showBetween lparen (showTerm t) rparen
showTerm' t              = showTerm t

showAbs :: Strictness -> Var -> Term -> ShowS
showAbs s v t =
  showStrictness s . showVar v .
  case t of
    AbsT s' v' t' -> showSpace . showAbs s' v' t'
    _             -> showSpace . showChar lambdaSep . showSpace . showTerm t
