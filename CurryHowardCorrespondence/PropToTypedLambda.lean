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


def TranslateTheoryToContext : List Formula →  Context
| [] => Context.Empty
| [f] => Context.Cons (FormulaNamig f) (FormulaTyping f) Context.Empty
| f::fs => Context.Cons (FormulaNamig f) (FormulaTyping f) (TranslateTheoryToContext fs)

def TranslateProofToTerm : Proof → Terms
| Proof.Axiom f => Terms.Var (FormulaNamig f) (FormulaTyping f)
| Proof.AndIntro f p q => Terms.Pair (TranslateProofToTerm p) (TranslateProofToTerm q)
| Proof.AndElim1 f p => Terms.Fst (TranslateProofToTerm p)
| Proof.AndElim2 f p => Terms.Snd (TranslateProofToTerm p)
| Proof.OrIntro1 f p => match f with
  | Formula.Or f1 _ => Terms.Inl (TranslateProofToTerm p) (FormulaTyping f1) (FormulaTyping f)
  | _ => Terms.EmptyElim (Terms.Var "Error" Types.Empty) (Terms.Var "Error" Types.Empty)
| Proof.OrIntro2 f p => match f with
  | Formula.Or _ f2 => Terms.Inr (TranslateProofToTerm p) (FormulaTyping f2) (FormulaTyping f)
  | _ => Terms.EmptyElim (Terms.Var "Error" Types.Empty) (Terms.Var "Error" Types.Empty)
| Proof.OrElim _ p q r => Terms.Case (TranslateProofToTerm p) (TranslateProofToTerm q) (TranslateProofToTerm r)
| Proof.ImplIntro f p => match f with
  | Formula.Impl f1 _ => Terms.Abs (FormulaNamig f1) (FormulaTyping f1) (TranslateProofToTerm p)
  | _ => Terms.EmptyElim (Terms.Var "Error" Types.Empty) (Terms.Var "Error" Types.Empty)
| Proof.ImplElim _ p q => Terms.App (TranslateProofToTerm p) (TranslateProofToTerm q)
| Proof.FalsumElim f p => Terms.EmptyElim (TranslateProofToTerm p) (Terms.Var (FormulaNamig f) (FormulaTyping f))

-- simple example of A ⊢ A to a : A^a ⊢ a : A
-- def example1 : Formula := Formula.Var (PropVar.fromString "A")
-- def example1Proof : Proof := Proof.Axiom example1
-- #eval example1Proof.toString
-- #eval (TranslateProofToTerm example1Proof).toString

-- #eval Proof.Check example1Proof [example1]
-- #eval Terms.GetIsInhabitant (TranslateTheoryToContext [example1]) (TranslateProofToTerm example1Proof) (FormulaTyping example1)
