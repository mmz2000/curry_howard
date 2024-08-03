-- This module serves as the root of the `CurryHowardCorrespondence` library.
-- Import modules here that should be built as part of the library.
import «CurryHowardCorrespondence».Basic

theorem soundness : ∀ {A: Term} {t: Types} {Γ:Context} , Inhabitable Γ t A -> Provable (contextToTheory Γ) (translateTypeToFormula t)
| _, t, (Context.Cons x _ Γ), Inhabitable.Var => by
  let Γ' := contextToTheory Γ
  let p := translateTypeToFormula t
  let P : Provable (Theory.Cons p Γ') p:= Provable.Axiom
  simp [contextToTheory]
  simp [p] at P
  exact P
| _, Types.Arrow t1 t2, Γ, Inhabitable.Abs h1 => by
  let P1 := soundness h1
  let Γ' := contextToTheory Γ
  let P: Provable Γ' (Formula.Impl (translateTypeToFormula t1) (translateTypeToFormula t2)):= Provable.ImpIntro P1
  simp [translateTypeToFormula]
  exact P
| _, t, Γ, Inhabitable.App h1 h2 => by
  let P1 := soundness h1
  let P2 := soundness h2
  simp [translateTypeToFormula] at P1
  let P:= Provable.ImpElim P1 P2
  exact P
| _, Types.Touples t1 t2, Γ, Inhabitable.Pair h1 h2 =>by
  let P1:= soundness h1
  let P2:= soundness h2
  let P:= Provable.AndIntro P1 P2
  simp [translateTypeToFormula]
  exact P
| _, t, Γ, Inhabitable.Proj1 h1 => by
  let P1 := soundness h1
  simp [translateTypeToFormula] at P1
  let P := Provable.AndElim1 P1
  exact P
| _, t, Γ, Inhabitable.Proj2 h1 => by
  let P1 := soundness h1
  simp [translateTypeToFormula] at P1
  let P := Provable.AndElim2 P1
  exact P
| _, Types.Either t1 t2, Γ, Inhabitable.Inl h1 => by
  let P1 := soundness h1
  let Γ' := contextToTheory Γ
  let P: Provable Γ' (Formula.Or (translateTypeToFormula t1) (translateTypeToFormula t2)):= Provable.OrIntro1 P1
  simp [translateTypeToFormula]
  exact P
| _, Types.Either t1 t2, Γ, Inhabitable.Inr h1 => by
  let P1 := soundness h1
  let Γ' := contextToTheory Γ
  let P: Provable Γ' (Formula.Or (translateTypeToFormula t1) (translateTypeToFormula t2)):= Provable.OrIntro2 P1
  simp [translateTypeToFormula]
  exact P
| _, t, Γ, Inhabitable.Case h1 h2 h3 => by
  let P1 := soundness h1
  let P2 := soundness h2
  let P3 := soundness h3
  simp [translateTypeToFormula] at P1
  simp [contextToTheory] at P2
  simp [contextToTheory] at P3
  let P := Provable.OrElim P1 P2 P3
  exact P
| _, t, Γ, Inhabitable.Absurd h1 => by
  let P1 := soundness h1
  let Γ' := contextToTheory Γ
  let P: Provable Γ' (translateTypeToFormula t):= Provable.false_elim P1
  exact P

theorem completeness : ∀ {p : Formula} {Γ: Theory}, (h : Provable Γ p) → ∃ (A: Term) , Inhabitable (theoryToContext Γ) (translateFormulaToType p) A
| p, (Theory.Cons _ Γ), Provable.Axiom => by
  let Γ' := theoryToContext Γ
  let t := translateFormulaToType p
  let p' := p.toString

  let A := Term.Var p'
  let inh : Inhabitable (Context.Cons p' t Γ') t A := Inhabitable.Var
  simp [Γ'] at inh
  exact ⟨A, inh⟩
| Formula.And p q, Γ, Provable.AndIntro h1 h2  => by
  let ⟨A1, inh1⟩ := completeness h1
  let ⟨A2, inh2⟩ := completeness h2
  let A := Term.Pair A1 A2
  let inh := Inhabitable.Pair inh1 inh2
  simp [translateFormulaToType]
  exact ⟨A, inh⟩
| Formula.Or p q, Γ, Provable.OrIntro1 h1 => by
  let ⟨A1, inh1⟩ := completeness h1
  let A:= Term.Inl A1 (translateFormulaToType p) (translateFormulaToType q)
  let inh :Inhabitable (theoryToContext Γ) (Types.Either (translateFormulaToType p) (translateFormulaToType q)) A := Inhabitable.Inl inh1
  simp [translateFormulaToType]
  exact ⟨A, inh⟩
| Formula.Or p q, Γ, Provable.OrIntro2 h1 => by
  let ⟨A1, inh1⟩ := completeness h1
  let A:= Term.Inr A1 (translateFormulaToType p) (translateFormulaToType q)
  let inh :Inhabitable (theoryToContext Γ) (Types.Either (translateFormulaToType p) (translateFormulaToType q)) A := Inhabitable.Inr inh1
  simp [translateFormulaToType]
  exact ⟨A, inh⟩
| Formula.Impl p q, Γ, Provable.ImpIntro h1 => by
  let ⟨A1, inh1⟩ := completeness h1
  simp [theoryToContext] at inh1
  let inh := Inhabitable.Abs inh1
  let A := Term.Abs (p.toString) (translateFormulaToType p) A1
  exact ⟨A, inh⟩
| p, Γ, Provable.false_elim h => by
  let ⟨A1, inh1⟩ := completeness h
  simp [translateFormulaToType] at inh1
  let A := Term.Absurd (translateFormulaToType p) A1
  let inh :Inhabitable (theoryToContext Γ) (translateFormulaToType p) A := Inhabitable.Absurd inh1
  exact ⟨A, inh⟩
| p, Γ, Provable.ImpElim h1 h2 => by
  let ⟨A1, inh1⟩ := completeness h1
  let ⟨A2, inh2⟩ := completeness h2
  simp [translateFormulaToType] at inh1
  let inh := Inhabitable.App inh1 inh2
  let A := Term.App A1 A2
  exact ⟨A, inh⟩
| p, Γ, Provable.OrElim h1 h2 h3 => by
  let ⟨A1, inh1⟩ := completeness h1
  let ⟨A2, inh2⟩ := completeness h2
  let ⟨A3, inh3⟩ := completeness h3
  simp [translateFormulaToType] at inh1
  simp [theoryToContext] at inh2
  simp [theoryToContext] at inh3
  let inh := Inhabitable.Case inh1 inh2 inh3
  let A := getInhabitableTerm inh
  exact ⟨A, inh⟩
| p , Γ, Provable.AndElim1 h1 => by
  let ⟨A1, inh1⟩ := completeness h1
  let A := Term.Proj1 A1
  let inh := Inhabitable.Proj1 inh1
  exact ⟨A, inh⟩
| p, Γ, Provable.AndElim2 h1 => by
  let ⟨A1, inh1⟩ := completeness h1
  let A := Term.Proj2 A1
  let inh := Inhabitable.Proj2 inh1
  exact ⟨A, inh⟩
