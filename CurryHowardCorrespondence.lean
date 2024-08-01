-- This module serves as the root of the `CurryHowardCorrespondence` library.
-- Import modules here that should be built as part of the library.
import «CurryHowardCorrespondence».Basic

theorem EQRemainsAfterTranslationTheory: ∀ {Γ Γ': Theory}, Γ = Γ' → theoryToContext Γ = theoryToContext Γ' := by
  intro Γ Γ' h
  induction h
  simp




-- theorem soundness : ∀ {p : Formula} {Γ: Theory}, (h : Provable Γ p) → ∃ (A: Term) (Γ': Context) (t: Types), Inhabitable (theoryToContext Γ) (translateFormulaToType t) A
