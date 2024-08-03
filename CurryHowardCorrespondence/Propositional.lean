inductive Formula : Type
| Var : String → Formula
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
instance fbeq : BEq Formula := ⟨Formula.eq⟩

def Formula.toString : Formula → String
| Formula.Var v => v
| Formula.And p q => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
| Formula.Or p q => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
| Formula.Impl p q => "(" ++ toString p ++ " → " ++ toString q ++ ")"
| Formula.Falsum => "⊥"

inductive Theory : Type
| Empty : Theory
| Cons : Formula → Theory → Theory

def Theory.contains : Theory → Formula → Bool
| Theory.Empty, _ => false
| Theory.Cons f Γ, f' => f == f' || contains Γ f'

def Theory.concat : Theory → Theory → Theory
| Theory.Empty, Γ => Γ
| Theory.Cons f Γ, Γ' => Theory.Cons f (concat Γ Γ')

def Theory.IsSub : Theory → Theory → Bool
| Theory.Empty, _ => true
| Theory.Cons f Γ, Γ' => Theory.contains Γ' f && IsSub Γ Γ'

def Theory.BEq : Theory → Theory → Bool := λ Γ Γ' => Theory.IsSub Γ Γ' && Theory.IsSub Γ' Γ

inductive Provable : Theory → Formula → Prop
| Axiom {Γ f} : Provable (Theory.Cons f Γ) f
| AndIntro {Γ p q}  (h1 : Provable Γ p) (h2: Provable Γ q) : Provable Γ (Formula.And p q)
| AndElim1 {Γ p q} (h : Provable Γ (Formula.And p q)) : Provable Γ p
| AndElim2 {Γ p q} (h : Provable Γ (Formula.And p q)) : Provable Γ q
| OrIntro1 {Γ p q} (h : Provable Γ p) : Provable Γ (Formula.Or p q)
| OrIntro2 {Γ p q} (h : Provable Γ q) : Provable Γ (Formula.Or p q)
| OrElim {Γ p q r} (h1 : Provable Γ (Formula.Or p q)) (h2 : Provable (Theory.Cons p Γ) r) (h3 : Provable (Theory.Cons q Γ) r) : Provable Γ r
| ImpElim {Γ p q} (h1 : Provable Γ (Formula.Impl p q)) (h2 : Provable Γ p) : Provable Γ q
| ImpIntro {Γ p q} (h : Provable (Theory.Cons p Γ) q) : Provable Γ (Formula.Impl p q)
| false_elim {Γ p} (h : Provable Γ Formula.Falsum) : Provable Γ p

def getProvableFormula : Provable Γ p -> Formula
| _ => p
