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
| Terms.App _ e1 e2 => Formula.Impl (TermsToFormula e1) (TermsToFormula e2)
| Terms.Pair _ e1 e2 => Formula.And (TermsToFormula e1) (TermsToFormula e2)
| Terms.Fst _ e => match e with
  | Terms.Pair _ e1 _ => TermsToFormula e1
  | _ => Formula.Falsum
| Terms.Snd _ e => match e with
  | Terms.Pair _ _ e2 => TermsToFormula e2
  | _ => Formula.Falsum
| Terms.Inl _ t1 t2 => Formula.Or (TypesToFormula t1) (TypesToFormula t2)
| Terms.Inr _ t1 t2 => Formula.Or (TypesToFormula t1) (TypesToFormula t2)
| Terms.Case _ e1 e2 e3 => Formula.Impl (Formula.Or (TermsToFormula e1) (TermsToFormula e2)) (TermsToFormula e3)
| Terms.Unit => Formula.Impl Formula.Falsum Formula.Falsum
| Terms.EmptyElim t _ _ => TypesToFormula t

def TermsToProof : Terms → Proof
| Terms.Var _ t => Proof.Axiom (TypesToFormula t)
| Terms.Abs _ t e => Proof.ImplIntro (Formula.Impl (TypesToFormula t) (TermsToFormula e)) (TermsToProof e)
| Terms.App t e1 e2 => Proof.ImplElim (TypesToFormula t) (TermsToProof e1) (TermsToProof e2)
| Terms.Pair t e1 e2 => Proof.AndIntro (TypesToFormula t) (TermsToProof e1) (TermsToProof e2)
| Terms.Fst t e => Proof.AndElim1 (TypesToFormula t) (TermsToProof e)
| Terms.Snd t e => Proof.AndElim2 (TypesToFormula t) (TermsToProof e)
| Terms.Inl e t1 t2 => Proof.OrIntro1 (Formula.Or (TypesToFormula t1) (TypesToFormula t2)) (TermsToProof e)
| Terms.Inr e t1 t2 => Proof.OrIntro2 (Formula.Or (TypesToFormula t1) (TypesToFormula t2)) (TermsToProof e)
| Terms.Case t e1 e2 e3 => Proof.OrElim (TypesToFormula t) (TermsToProof e2) (TermsToProof e3) (TermsToProof e1)
| Terms.Unit => Proof.ImplIntro (Formula.Impl Formula.Falsum Formula.Falsum) (Proof.Axiom (Formula.Impl Formula.Falsum Formula.Falsum))
| Terms.EmptyElim t a _ => Proof.FalsumElim (TypesToFormula t) (TermsToProof a)

def ContextToTheory : Context → List Formula
| Context.Empty => []
| Context.Cons _ A Γ => (TypesToFormula A)::(ContextToTheory Γ)
