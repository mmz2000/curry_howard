inductive PropVar : Type
| fromString : String → PropVar

def PropVar.eq : PropVar → PropVar → Bool
| PropVar.fromString s1, PropVar.fromString s2 => s1 == s2

-- BEq instance for PropVar
instance : BEq PropVar := ⟨PropVar.eq⟩

def PropVar.toString : PropVar → String
| PropVar.fromString s => s

instance : ToString PropVar := ⟨PropVar.toString⟩

inductive Formula : Type
| Var : PropVar → Formula
| And : Formula → Formula → Formula
| Or : Formula → Formula → Formula
| Impl : Formula → Formula → Formula
| Falsum : Formula

def Formula.eq : Formula → Formula → Bool
| Formula.Var v1, Formula.Var v2 => v1 == v2
| Formula.And f1 g1, Formula.And f2 g2 => Formula.eq f1 f2 && Formula.eq g1 g2
| Formula.Or f1 g1, Formula.Or f2 g2 => Formula.eq f1 f2 && Formula.eq g1 g2
| Formula.Impl f1 g1, Formula.Impl f2 g2 => Formula.eq f1 f2 && Formula.eq g1 g2
| Formula.Falsum, Formula.Falsum => true
| _, _ => false

-- BEq instance for Formula
instance : BEq Formula := ⟨Formula.eq⟩


inductive Proof : Type
| Axiom : Formula → Proof
| AndIntro : Formula → Proof → Proof → Proof
| AndElim1 : Formula → Proof → Proof
| AndElim2 : Formula → Proof → Proof
| OrIntro1 : Formula → Proof → Proof
| OrIntro2 : Formula → Proof → Proof
| OrElim : Formula → Proof → Proof → Proof → Proof
| ImplIntro : Formula → Proof → Proof
| ImplElim : Formula → Proof → Proof → Proof
| FalsumElim : Formula → Proof → Proof


def Formula.toString : Formula → String
| Formula.Var v => v.toString
| Formula.And p q => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
| Formula.Or p q => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
| Formula.Impl p q => "(" ++ toString p ++ " → " ++ toString q ++ ")"
| Formula.Falsum => "⊥"


def listFormulaToString : List Formula → String
| [] => ""
| [f] => f.toString
| f :: fs => f.toString ++ ", " ++ listFormulaToString fs

def Proof.toString : Proof → String
| Proof.Axiom f => "Axiom " ++ f.toString
| Proof.AndIntro f p q => "AndIntro " ++ f.toString ++ "by " ++ p.toString ++ " and " ++ q.toString
| Proof.AndElim1 f p => "AndElim1 " ++ f.toString ++ " by " ++ p.toString
| Proof.AndElim2 f p => "AndElim2 " ++ f.toString ++ " by " ++ p.toString
| Proof.OrIntro1 f p => "OrIntro1 " ++ f.toString ++ " by " ++ p.toString
| Proof.OrIntro2 f p => "OrIntro2 " ++ f.toString ++ " by " ++ p.toString
| Proof.OrElim f p q r => "OrElim " ++ f.toString ++ " by " ++ p.toString ++ " and " ++ q.toString ++ " and " ++ r.toString
| Proof.ImplIntro f p => "ImplIntro " ++ f.toString ++ " by " ++ p.toString
| Proof.ImplElim f p q => "ImplElim " ++ f.toString ++ " by " ++ p.toString ++ " and " ++ q.toString
| Proof.FalsumElim f p => "FalsumElim " ++ f.toString ++ " by " ++ p.toString

def Proof.getFormula : Proof → Formula
| Proof.Axiom f => f
| Proof.AndIntro f _ _ => f
| Proof.AndElim1 f _ => f
| Proof.AndElim2 f _ => f
| Proof.OrIntro1 f _ => f
| Proof.OrIntro2 f _ => f
| Proof.OrElim f _ _ _ => f
| Proof.ImplIntro f _ => f
| Proof.ImplElim f _ _ => f
| Proof.FalsumElim f _ => f


def Proof.Check : Proof → List Formula → Bool
| Proof.Axiom f, fs => fs.contains f
| Proof.AndIntro f p q, fs => Proof.Check p fs && Proof.Check q fs && match f with
  | Formula.And f1 f2 => f1 == p.getFormula && f2 == q.getFormula
  | _ => false
| Proof.AndElim1 f p, fs => Proof.Check p fs && match getFormula p with
  | Formula.And f1 _ => f1 == f
  | _ => false
| Proof.AndElim2 f p, fs => Proof.Check p fs && match getFormula p with
  | Formula.And _ f2 => f2 == f
  | _ => false
| Proof.OrIntro1 f p, fs => Proof.Check p fs && match f with
  | Formula.Or f1 _ => f1 == p.getFormula
  | _ => false
| Proof.OrIntro2 f p, fs => Proof.Check p fs && match f with
  | Formula.Or _ f2 => f2 == p.getFormula
  | _ => false
| Proof.OrElim f p q r, fs =>Proof.Check r fs && match getFormula r with
  | Formula.Or f1 f2 => Proof.Check p (fs.append ([f1])) && Proof.Check q (fs.append ([f2])) && (f == getFormula p || Formula.Impl f1 f == getFormula p) && (f == getFormula q || Formula.Impl f2 f == getFormula q)
  | _ => false
| Proof.ImplIntro f p, fs => match f with
  | Formula.Impl f1 f2 => Proof.Check p (fs.append ([f1])) && f2 == getFormula p
  | _ => false
| Proof.ImplElim f p q, fs => match getFormula p with
  | Formula.Impl f1 f2 => Proof.Check p fs && Proof.Check q fs && f1 == getFormula q && f2 == f
  | _ => false
| Proof.FalsumElim f p, fs => Proof.Check p fs && match getFormula p with
  | Formula.Falsum => f == f
  | _ => false

-- -- simple example of A ⊢ A
-- def example1 : Formula := Formula.Var (PropVar.fromString "A")
-- def example1Proof : Proof := Proof.Axiom example1

-- #eval example1.toString
-- #eval example1Proof.toString
-- #eval Proof.Check example1Proof [example1]

-- -- simple example of A ⊢ A ∧ A
-- def example2 : Formula := Formula.And (Formula.Var (PropVar.fromString "A")) (Formula.Var (PropVar.fromString "A"))
-- def example2Proof : Proof := Proof.AndIntro example2 (Proof.Axiom (Formula.Var (PropVar.fromString "A"))) (Proof.Axiom (Formula.Var (PropVar.fromString "A")))
-- #eval example2Proof.toString
-- #eval Proof.Check example2Proof [example1]

-- -- simple example of ⊢ A → A
-- def example3 : Formula := Formula.Impl (Formula.Var (PropVar.fromString "A")) (Formula.Var (PropVar.fromString "A"))
-- def example3Proof : Proof := Proof.ImplIntro example3 (Proof.Axiom (Formula.Var (PropVar.fromString "A")))
-- #eval example3Proof.toString
-- #eval Proof.Check example3Proof []

-- -- simple example of A , A->B ⊢ B
-- def AxiomA : Formula := Formula.Var (PropVar.fromString "A")
-- def AxiomAImplB : Formula := Formula.Impl (Formula.Var (PropVar.fromString "A")) (Formula.Var (PropVar.fromString "B"))
-- def AxiomaticContext : List Formula := [AxiomA, AxiomAImplB]
-- def ProofOfB : Proof := Proof.ImplElim (Formula.Var (PropVar.fromString "B")) (Proof.Axiom AxiomAImplB) (Proof.Axiom AxiomA)
-- #eval ProofOfB.toString
-- #eval Proof.Check ProofOfB AxiomaticContext

-- -- simple example of or elimination
-- def axiomaticOr : Formula := Formula.Or (Formula.Var (PropVar.fromString "A")) (Formula.Var (PropVar.fromString "B"))
-- #eval axiomaticOr.toString
-- def routeA : Formula := Formula.Impl (Formula.Var (PropVar.fromString "A")) (Formula.Var (PropVar.fromString "C"))
-- #eval routeA.toString
-- def routeB : Formula := Formula.Impl (Formula.Var (PropVar.fromString "B")) (Formula.Var (PropVar.fromString "C"))
-- #eval routeB.toString
-- def axiomaticProofOfOr : Proof := Proof.Axiom axiomaticOr
-- #eval axiomaticProofOfOr.toString
-- def routeAArrowC : Proof := Proof.ImplElim (Formula.Var (PropVar.fromString "C")) (Proof.Axiom routeA) (Proof.Axiom (Formula.Var (PropVar.fromString "A")))
-- #eval routeAArrowC.toString
-- def routeBArrowC : Proof := Proof.ImplElim (Formula.Var (PropVar.fromString "C")) (Proof.Axiom routeB) (Proof.Axiom (Formula.Var (PropVar.fromString "B")))
-- #eval routeBArrowC.toString
-- def orElimProof : Proof := Proof.OrElim (Formula.Var (PropVar.fromString "C")) routeAArrowC routeBArrowC axiomaticProofOfOr
-- #eval orElimProof.toString
-- #eval Proof.Check orElimProof [axiomaticOr, routeA, routeB]

-- -- simple example of exfalso quodlibet
-- def example5 : Formula := Formula.Impl Formula.Falsum (Formula.Var (PropVar.fromString "A"))
-- #eval example5.toString
-- def example5Proof : Proof := Proof.ImplElim (Formula.Var (PropVar.fromString "A"))  (Proof.Axiom example5) (Proof.Axiom Formula.Falsum)
-- #eval example5Proof.toString
-- #eval Proof.Check example5Proof [Formula.Falsum, example5]

-- def example6Proof : Proof := Proof.FalsumElim (Formula.Var (PropVar.fromString "A")) (Proof.Axiom Formula.Falsum)

-- #eval example6Proof.toString
-- #eval Proof.Check example6Proof [Formula.Falsum]
