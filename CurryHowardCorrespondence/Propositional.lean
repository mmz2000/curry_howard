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
instance : BEq Formula := ⟨Formula.eq⟩

def Formula.toString : Formula → String
| Formula.Var v => v
| Formula.And p q => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
| Formula.Or p q => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
| Formula.Impl p q => "(" ++ toString p ++ " → " ++ toString q ++ ")"
| Formula.Falsum => "⊥"


inductive Provable : List Formula → Formula → Prop
| Axiom {Γ f} (h : Γ.contains f) : Provable Γ f
| AndIntor {Γ p q}  (h1 : Provable Γ p) (h2: Provable Γ q) : Provable Γ (Formula.And p q)
| AndElim1 {Γ p q} (h : Provable Γ (Formula.And p q)) : Provable Γ p
| AndElim2 {Γ p q} (h : Provable Γ (Formula.And p q)) : Provable Γ q
| OrIntro1 {Γ p q} (h : Provable Γ p) : Provable Γ (Formula.Or p q)
| OrIntro2 {Γ p q} (h : Provable Γ q) : Provable Γ (Formula.Or p q)
| OrElim {Γ p q r} (h1 : Provable Γ (Formula.Or p q)) (h2 : Provable (Γ.concat p) r) (h3 : Provable (Γ.concat q) r) : Provable Γ r
| ImpElim {Γ p q} (h1 : Provable Γ (Formula.Impl p q)) (h2 : Provable Γ q) : Provable Γ q
| ImpIntro {Γ p q} (h : Provable (Γ.concat p) q) : Provable Γ (Formula.Impl p q)
| false_elim {Γ p} (h : Provable Γ Formula.Falsum) : Provable Γ p
