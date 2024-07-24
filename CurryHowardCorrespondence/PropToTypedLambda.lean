import CurryHowardCorrespondence.Propositional
import CurryHowardCorrespondence.TypedLambda



def VarNaming: PropVar → String
| PropVar.fromString s => s

def VarTyping: PropVar → Types
| f => Types.TypeVar f.toString

def FormulaNamig: Formula → String
| f => f.toString.toUpper ++ "^" ++ f.toString.toLower

def FormulaTyping: Formula → Types
| Formula.Var p => Types.TypeVar (VarNaming p)
| Formula.And p q => Types.Touples (FormulaTyping p) (FormulaTyping q)
| Formula.Impl p q => Types.Arrow (FormulaTyping p) (FormulaTyping q)
| Formula.Falsum => Types.Empty
| Formula.Or p q => Types.Either (FormulaTyping p) (FormulaTyping q)


def FormulaToTerm : Formula → Terms
| Formula.Var v => Terms.Var (VarNaming v) (VarTyping v)
| Formula.And f1 f2 => Terms.Pair (FormulaToTerm f1) (FormulaToTerm f2)
| Formula.Or f1 f2 => Terms.Inl (FormulaToTerm f1) (FormulaTyping f1) (FormulaTyping f2)
| Formula.Impl f1 f2 => Terms.Abs (FormulaNamig f1) (FormulaTyping f1) (FormulaToTerm f2)
| Formula.Falsum => Terms.Empty

def TranslateTheoryToContext : List Formula →  Context
| [] => Context.Empty
| [f] => Context.Cons (FormulaNamig f) (FormulaTyping f) Context.Empty
| f::fs => Context.Cons (FormulaNamig f) (FormulaTyping f) (TranslateTheoryToContext fs)
