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


inductive Proof : List Formula →  Formula → Type
| Axiom : ∀ {Γ : List Formula} {p : Formula}, List Formula →  Formula → Proof (p::Γ) p
| AndIntro : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ p → Proof Γ q → Proof Γ (Formula.And p q)
| AndElim1 : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ (Formula.And p q) → Proof Γ p
| AndElim2 : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ (Formula.And p q) → Proof Γ q
| OrIntro1 : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ p → Proof Γ (Formula.Or p q)
| OrIntro2 : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ q → Proof Γ (Formula.Or p q)
| OrElim : ∀ {Γ : List Formula} {p q r : Formula}, Proof Γ (Formula.Or p q) → Proof (p :: Γ) r → Proof (q :: Γ) r → Proof Γ r
| ImplIntro : ∀ {Γ : List Formula} {p q : Formula}, Proof (p :: Γ) q → Proof Γ (Formula.Impl p q)
| ImplElim : ∀ {Γ : List Formula} {p q : Formula}, Proof Γ (Formula.Impl p q) → Proof Γ p → Proof Γ q
| FalsumElim : ∀ {Γ : List Formula} {p : Formula}, Proof Γ Formula.Falsum → Proof Γ p

instance sampleProof1 : Proof [sampleFormula1] sampleFormula1 := Proof.Axiom [sampleFormula1] sampleFormula1
instance sampleProof2 : Proof [] (Formula.Impl sampleFormula1 sampleFormula1) := Proof.ImplIntro sampleProof1

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

def Proof.toString : ∀ {Γ : List Formula} {p : Formula}, Proof Γ p → String
| _ ,_ ,Proof.Axiom Γ p => "Axiom: " ++ listFormulaToString Γ ++ " ⊢ " ++ p.toString
| Γ ,Formula.And p q ,Proof.AndIntro proof1 proof2 =>"(" ++ proof1.toString  ++ proof2.toString ++ ") ==>" ++ "AndIntro: " ++ listFormulaToString Γ ++ " ⊢ " ++ (Formula.And p q).toString
| Γ ,q ,Proof.AndElim1 p => "(" ++p.toString++ ") ==>" ++ "AndElim1: " ++ listFormulaToString Γ ++ " ⊢ " ++ q.toString
| Γ ,q ,Proof.AndElim2 p => "(" ++p.toString++ ") ==>" ++ "AndElim2: " ++ listFormulaToString Γ ++ " ⊢ " ++ q.toString
| Γ ,Formula.Or s r ,Proof.OrIntro1 p => "(" ++p.toString++ ") ==>" ++ "OrIntro1: " ++ listFormulaToString Γ ++ " ⊢ " ++ (Formula.Or s r).toString
| Γ ,Formula.Or s r ,Proof.OrIntro2 p =>"(" ++ p.toString++ ") ==>" ++ "OrIntro2: " ++ listFormulaToString Γ ++ " ⊢ " ++ (Formula.Or s r).toString
| Γ ,f ,Proof.OrElim p q r => "(" ++p.toString ++ q.toString ++ r.toString++ ") ==>" ++ "OrElim: " ++ listFormulaToString Γ ++ " ⊢ " ++ f.toString
| Γ ,Formula.Impl r s ,Proof.ImplIntro p =>"(" ++ p.toString++ ") ==>" ++ "ImplIntro: " ++ listFormulaToString Γ ++ " ⊢ " ++ (Formula.Impl r s).toString
| Γ ,r ,Proof.ImplElim p q => "(" ++p.toString ++ q.toString++ ") ==>" ++ "ImplElim: " ++ listFormulaToString Γ ++ " ⊢ " ++ r.toString
| Γ ,f ,Proof.FalsumElim p =>"(" ++ p.toString++ ") ==>" ++ "FalsumElim: " ++ listFormulaToString Γ ++ " ⊢ " ++ f.toString

def CheckProof : ∀ {Γ : List Formula} {p : Formula}, Proof Γ p → Bool
| _ ,_ ,Proof.Axiom Γ p => Γ.contains p
| _ ,Formula.And _ _ ,Proof.AndIntro proof1 proof2 => CheckProof proof1 && CheckProof proof2
| _ ,_ ,Proof.AndElim1 p => CheckProof p
| _ ,_ ,Proof.AndElim2 p => CheckProof p
| _ ,Formula.Or _ _ ,Proof.OrIntro1 p => CheckProof p
| _ ,Formula.Or _ _ ,Proof.OrIntro2 p => CheckProof p
| _ ,_ ,Proof.OrElim p q r => CheckProof p && CheckProof q && CheckProof r
| _ ,Formula.Impl _ _ ,Proof.ImplIntro p => CheckProof p
| _ ,_ ,Proof.ImplElim p q => CheckProof p && CheckProof q
| _ ,_ ,Proof.FalsumElim p => CheckProof p
