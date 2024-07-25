import CurryHowardCorrespondence.Propositional
import CurryHowardCorrespondence.TypedLambda


def TypesToFormula : Types → Formula
| Types.TypeVar x => Formula.Var (PropVar.fromString x)
| Types.Touples t1 t2 => Formula.And (TypesToFormula t1) (TypesToFormula t2)
| Types.Either t1 t2 => Formula.Or (TypesToFormula t1) (TypesToFormula t2)
| Types.Arrow t1 t2 => Formula.Impl (TypesToFormula t1) (TypesToFormula t2)
| Types.Unit => Formula.Var (PropVar.fromString "Unit")
| Types.Empty => Formula.Falsum

def TermsToFormula : Terms → Formula
| Terms.Var _ t => TypesToFormula t
| Terms.Abs _ t e => Formula.Impl (TypesToFormula t) (TermsToFormula e)
| Terms.App e1 e2 => Formula.Impl (TermsToFormula e1) (TermsToFormula e2)
| Terms.Pair e1 e2 => Formula.And (TermsToFormula e1) (TermsToFormula e2)
| Terms.Fst e => match e with
  | Terms.Pair e1 _ => TermsToFormula e1
  | _ => Formula.Falsum
| Terms.Snd e => match e with
  | Terms.Pair _ e2 => TermsToFormula e2
  | _ => Formula.Falsum
| Terms.Inl _ t1 t2 => Formula.Or (TypesToFormula t1) (TypesToFormula t2)
| Terms.Inr _ t1 t2 => Formula.Or (TypesToFormula t1) (TypesToFormula t2)
| Terms.Case e1 e2 e3 => Formula.Impl (Formula.Or (TermsToFormula e1) (TermsToFormula e2)) (TermsToFormula e3)
| Terms.Unit => Formula.Impl Formula.Falsum Formula.Falsum
| Terms.EmptyElim a b => Formula.Impl (TermsToFormula b) (TermsToFormula a)

def TermsToProof : Terms → Proof
| Terms.Var _ t => Proof.Axiom (TypesToFormula t)
| Terms.Abs _ t e => Proof.ImplIntro (TypesToFormula t) (TermsToProof e)
| Terms.App e1 e2 => match e1 with
  | Terms.Abs _ _ e => Proof.ImplElim (TermsToFormula e) (TermsToProof e) (TermsToProof e2)
  | _ => Proof.Axiom (Formula.Falsum)
| Terms.Pair e1 e2 => Proof.AndIntro (Formula.And (TermsToFormula e1) (TermsToFormula e2)) (TermsToProof e1) (TermsToProof e2)
| Terms.Fst e => Proof.AndElim1 (TermsToFormula e) (TermsToProof e)
| Terms.Snd e => Proof.AndElim2 (TermsToFormula e) (TermsToProof e)
| Terms.Inl e t1 t2 => Proof.OrIntro1 (Formula.Or (TypesToFormula t1) (TypesToFormula t2)) (TermsToProof e)
| Terms.Inr e t1 t2 => Proof.OrIntro2 (Formula.Or (TypesToFormula t1) (TypesToFormula t2)) (TermsToProof e)
| Terms.Case e1 e2 e3 => Proof.OrElim (TermsToFormula e3) (TermsToProof e1) (TermsToProof e2) (TermsToProof e3)
| Terms.Unit => Proof.ImplIntro (Formula.Impl Formula.Falsum Formula.Falsum) (Proof.Axiom (Formula.Impl Formula.Falsum Formula.Falsum))
| Terms.EmptyElim a b => Proof.FalsumElim (TermsToFormula b) (TermsToProof a)

def ContextToTheory : Context → List Formula
| Context.Empty => []
| Context.Cons _ A Γ => (TypesToFormula A)::(ContextToTheory Γ)

-- simple example of a:A ⊢ a : A to a : A ⊢ A

-- def example1 : Terms := Terms.Var "a" (Types.TypeVar "A")
-- def example1Proof : Proof := TermsToProof example1
-- #eval example1.toString
-- #eval example1Proof.toString
-- def context : Context := Context.Cons "a" (Types.TypeVar "A") Context.Empty
-- def theory_: List Formula := ContextToTheory context
-- #eval Proof.Check example1Proof theory_
-- #eval Terms.GetIsInhabitant context example1 (Types.TypeVar "A")
