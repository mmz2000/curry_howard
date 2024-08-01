import CurryHowardCorrespondence.Propositional
import CurryHowardCorrespondence.TypedLambda

def translateFormulaToType : Formula → Types
| Formula.Var v => Types.TypeVar (typeVarNames.fromPropVarNames v)
| Formula.And p q => Types.Touples (translateFormulaToType p) (translateFormulaToType q)
| Formula.Or p q => Types.Either (translateFormulaToType p) (translateFormulaToType q)
| Formula.Impl p q => Types.Arrow (translateFormulaToType p) (translateFormulaToType q)
| Formula.Falsum => Types.Empty

def translateTypeToFormula : Types → Formula
| Types.TypeVar v => Formula.Var v.toPropVarNames
| Types.Touples p q => Formula.And (translateTypeToFormula p) (translateTypeToFormula q)
| Types.Either p q => Formula.Or (translateTypeToFormula p) (translateTypeToFormula q)
| Types.Arrow p q => Formula.Impl (translateTypeToFormula p) (translateTypeToFormula q)
| Types.Empty => Formula.Falsum

theorem dsimpfbeq: Formula.eq p q → p == q := by
  simp [fbeq]
  intro h
  rw [h]

theorem f2t_eq: ∀ {p q: Formula}, p == q → (translateFormulaToType p) == (translateFormulaToType q)
| Formula.Var p, Formula.Var q => by
  intro h
  simp [fbeq] at h
  simp [tbeq]
  simp [EqualTypes]
  simp [Formula.eq] at h
  rw [eq_pvname_eq_tvname]
  rw [h]
| Formula.Var p, Formula.And _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Var p, Formula.Impl _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Var p, Formula.Or _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Var p, Formula.Falsum => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Falsum, Formula.Falsum  => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Falsum, Formula.Var _  => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Falsum, Formula.And _ _  => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Falsum, Formula.Or _ _  => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Falsum, Formula.Impl _ _  => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.And p q, Formula.And p' q' => by
  intro h
  simp [translateFormulaToType]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [tbeq]
  simp [EqualTypes]
  let hr' := dsimpfbeq hr
  let hl' := dsimpfbeq hl
  let l := f2t_eq hl'
  let r := f2t_eq hr'
  simp [tbeq] at l
  simp [tbeq] at r
  simp [r]
  simp [l]
| Formula.And _ _, Formula.Var _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.And _ _, Formula.Or _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.And _ _, Formula.Impl _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.And _ _, Formula.Falsum => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Impl p q, Formula.Impl p' q' => by
  intro h
  simp [translateFormulaToType]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [tbeq]
  simp [EqualTypes]
  let hr' := dsimpfbeq hr
  let hl' := dsimpfbeq hl
  let l := f2t_eq hl'
  let r := f2t_eq hr'
  simp [tbeq] at l
  simp [tbeq] at r
  simp [r]
  simp [l]
| Formula.Impl _ _, Formula.Var _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Impl _ _, Formula.Or _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Impl _ _, Formula.And _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Impl _ _, Formula.Falsum => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Or p q, Formula.Or p' q' => by
  intro h
  simp [translateFormulaToType]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [tbeq]
  simp [EqualTypes]
  let hr' := dsimpfbeq hr
  let hl' := dsimpfbeq hl
  let l := f2t_eq hl'
  let r := f2t_eq hr'
  simp [tbeq] at l
  simp [tbeq] at r
  simp [r]
  simp [l]
| Formula.Or _ _, Formula.Var _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Or _ _, Formula.Impl _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Or _ _, Formula.And _ _ => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h
| Formula.Or _ _, Formula.Falsum => by
  intro h
  simp [fbeq] at h
  simp [Formula.eq] at h

theorem f2t_eq2: ∀ {p q: Formula},(translateFormulaToType p) == (translateFormulaToType q) →  p == q
| Formula.Var p, Formula.Var q => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
  simp [fbeq]
  simp [Formula.eq]
  simp [typevarbeq]
  cases p
  cases q
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  rfl
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  cases q
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  rfl
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  cases q
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  rfl
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  cases q
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  simp [typeVarNames.fromPropVarNames, typeVarNames.eq]
  rfl
| Formula.Var _ , Formula.And _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Var _ , Formula.Or _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Var _ , Formula.Impl _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Var _ , Formula.Falsum => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Falsum , Formula.Falsum => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
  rfl
| Formula.Falsum, Formula.And _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Falsum, Formula.Or _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Falsum, Formula.Impl _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Falsum, Formula.Var _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Impl p q, Formula.Impl p' q' => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2t_eq2 hl
  let r:= f2t_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.Impl _ _, Formula.And _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Impl _ _, Formula.Or _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Impl _ _, Formula.Falsum => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Impl _ _, Formula.Var _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.And p q, Formula.And p' q' => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2t_eq2 hl
  let r:= f2t_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.And _ _, Formula.Impl _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.And _ _, Formula.Or _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.And _ _, Formula.Falsum => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.And _ _, Formula.Var _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Or p q, Formula.Or p' q' => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2t_eq2 hl
  let r:= f2t_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.Or _ _, Formula.Impl _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Or _ _, Formula.And _ _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Or _ _, Formula.Falsum => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
| Formula.Or _ _, Formula.Var _ => by
  simp [translateFormulaToType]
  simp [tbeq]
  simp [EqualTypes]
