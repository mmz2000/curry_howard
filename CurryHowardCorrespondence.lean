-- This module serves as the root of the `CurryHowardCorrespondence` library.
-- Import modules here that should be built as part of the library.
import «CurryHowardCorrespondence».Basic

theorem EQRemainsAfterTranslationTheory: ∀ {Γ Γ': Theory}, Γ = Γ' → theoryToContext Γ = theoryToContext Γ' := by
  intro Γ Γ' h
  induction h
  simp




theorem completeness : ∀ {p : Formula} {Γ: Theory}, (h : Provable Γ p) → ∃ (A: Term) , Inhabitable (theoryToContext Γ) (translateFormulaToType p) A
| p, Γ, Provable.Axiom h => by
  let Γ' := theoryToContext Γ
  let t := translateFormulaToType p
  let p' := translateFormulaToVarname p
  let h' : Γ'.getType p' == t:= by
    let h1 := t2c_cons h
    simp [Γ']
    exact h1
  let A := Term.Var p'
  let inh := Inhabitable.Var h'
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
  let A := Term.Abs (translateFormulaToVarname p) (translateFormulaToType p) A1
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
