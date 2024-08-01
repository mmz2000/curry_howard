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

theorem t2f_eq: ∀ {p q: Types}, p == q → (translateTypeToFormula p) == (translateTypeToFormula q)
| Types.TypeVar v, Types.TypeVar v' => by
  intro h
  simp [translateTypeToFormula]
  simp [fbeq]
  simp [Formula.eq]
  simp [tbeq] at h
  simp [EqualTypes] at h
  let h':= eq_tvname_eq_pvname2 h
  exact h'
| Types.TypeVar _, Types.Touples _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.TypeVar _, Types.Either _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.TypeVar _, Types.Arrow _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.TypeVar _, Types.Empty =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Empty, Types.Empty  => by
  simp [translateTypeToFormula]
  simp [fbeq]
  simp [Formula.eq]
| Types.Empty , Types.Touples _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Empty , Types.Either _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Empty , Types.Arrow _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Empty , Types.TypeVar _ =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Touples p q, Types.Touples p' q' => by
  intro h
  simp [tbeq, EqualTypes] at h
  simp [translateTypeToFormula,fbeq,Formula.eq]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq hl
  let r := t2f_eq hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Types.Touples _ _, Types.TypeVar _ =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Touples _ _, Types.Either _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Touples _ _, Types.Arrow _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Touples _ _, Types.Empty =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Either p q, Types.Either p' q' => by
  intro h
  simp [tbeq, EqualTypes] at h
  simp [translateTypeToFormula,fbeq,Formula.eq]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq hl
  let r := t2f_eq hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Types.Either _ _, Types.TypeVar _ =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Either _ _, Types.Touples _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Either _ _, Types.Arrow _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Either _ _, Types.Empty =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Arrow p q, Types.Arrow p' q' => by
  intro h
  simp [tbeq, EqualTypes] at h
  simp [translateTypeToFormula,fbeq,Formula.eq]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq hl
  let r := t2f_eq hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Types.Arrow _ _, Types.TypeVar _ =>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Arrow _ _, Types.Touples _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Arrow _ _, Types.Either _ _=>by
  simp [tbeq]
  simp [EqualTypes]
| Types.Arrow _ _, Types.Empty =>by
  simp [tbeq]
  simp [EqualTypes]

theorem t2f_eq2:  ∀ {p q: Types}, (translateTypeToFormula p) == (translateTypeToFormula q) → p == q
| Types.TypeVar v, Types.TypeVar v' => by
  intro h
  simp [translateTypeToFormula,fbeq,Formula.eq] at h
  simp [tbeq,EqualTypes]
  let h' := eq_pvname_eq_tvname2 h
  rw [h']
| Types.TypeVar _, Types.Touples _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.TypeVar _, Types.Either _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.TypeVar _, Types.Arrow _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.TypeVar _, Types.Empty =>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Empty, Types.Empty => by
  simp [tbeq,EqualTypes]
| Types.Empty, Types.Touples _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Empty, Types.Either _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Empty, Types.Arrow _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Empty, Types.TypeVar _ =>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Either p q, Types.Either p' q' => by
  intro h
  simp [translateTypeToFormula,fbeq,Formula.eq] at h
  simp [tbeq,EqualTypes]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq2 hl
  let r := t2f_eq2 hr
  simp [tbeq] at l
  simp [tbeq] at r
  rw [l,r]
  simp
| Types.Either _ _, Types.Touples _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Either _ _, Types.Empty=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Either _ _, Types.Arrow _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Either _ _, Types.TypeVar _ =>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Touples p q, Types.Touples p' q' => by
  intro h
  simp [translateTypeToFormula,fbeq,Formula.eq] at h
  simp [tbeq,EqualTypes]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq2 hl
  let r := t2f_eq2 hr
  simp [tbeq] at l
  simp [tbeq] at r
  rw [l,r]
  simp
| Types.Touples _ _, Types.Either _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Touples _ _, Types.Empty=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Touples _ _, Types.Arrow _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Touples _ _, Types.TypeVar _ =>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Arrow p q, Types.Arrow p' q' => by
  intro h
  simp [translateTypeToFormula,fbeq,Formula.eq] at h
  simp [tbeq,EqualTypes]
  let hl := h.left
  let hr := h.right
  let l := t2f_eq2 hl
  let r := t2f_eq2 hr
  simp [tbeq] at l
  simp [tbeq] at r
  rw [l,r]
  simp
| Types.Arrow _ _, Types.Either _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Arrow _ _, Types.Empty=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Arrow _ _, Types.Touples _ _=>by
  simp [translateTypeToFormula,fbeq,Formula.eq]
| Types.Arrow _ _, Types.TypeVar _ =>by
  simp [translateTypeToFormula,fbeq,Formula.eq]

def translateFormulaToVarname : Formula → VarName
| Formula.Var v => VarName.FromVarname (termVarNames.fromPropVarNames v)
| Formula.And p q => VarName.TouplesVarname (translateFormulaToVarname p) (translateFormulaToVarname q)
| Formula.Or p q => VarName.EitherVarname (translateFormulaToVarname p) (translateFormulaToVarname q)
| Formula.Impl p q => VarName.ArrowVarname (translateFormulaToVarname p) (translateFormulaToVarname q)
| Formula.Falsum => VarName.EmptyVarname

theorem f2v_eq: ∀ {p q: Formula}, p == q → (translateFormulaToVarname p) == (translateFormulaToVarname q)
| Formula.Var p, Formula.Var q => by
  intro h
  simp [fbeq] at h
  simp [Vbeq]
  simp [VarName.eq]
  simp [Formula.eq] at h
  let h' := eq_pvname_eq_tname h
  rw [h']
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
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
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
  simp [translateFormulaToVarname]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [Vbeq]
  simp [VarName.eq]
  let l := f2v_eq hl
  let r := f2v_eq hr
  simp [Vbeq] at l
  simp [Vbeq] at r
  rw [l]
  rw [r]
  simp
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
  simp [translateFormulaToVarname]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [Vbeq]
  simp [VarName.eq]
  let l := f2v_eq hl
  let r := f2v_eq hr
  simp [Vbeq] at l
  simp [Vbeq] at r
  rw [l]
  rw [r]
  simp
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
  simp [translateFormulaToVarname]
  simp [fbeq] at h
  simp [Formula.eq] at h
  let hr := h.right
  let hl := h.left
  simp [Vbeq]
  simp [VarName.eq]
  let l := f2v_eq hl
  let r := f2v_eq hr
  simp [Vbeq] at l
  simp [Vbeq] at r
  rw [l]
  rw [r]
  simp
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

theorem f2v_eq2: ∀ {p q: Formula},(translateFormulaToVarname p) == (translateFormulaToVarname q) →  p == q
| Formula.Var p, Formula.Var q => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
  simp [fbeq]
  simp [Formula.eq]
  simp [termvarbeq]
  cases p
  cases q
  simp [termVarNames.fromPropVarNames,termVarNames.eq,provpvarbeq,propVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  cases q
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  rfl
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  cases q
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  rfl
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  cases q
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  simp [termVarNames.fromPropVarNames, termVarNames.eq]
  rfl
| Formula.Var _ , Formula.And _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Var _ , Formula.Or _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Var _ , Formula.Impl _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Var _ , Formula.Falsum => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Falsum , Formula.Falsum => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
  rfl
| Formula.Falsum, Formula.And _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Falsum, Formula.Or _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Falsum, Formula.Impl _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Falsum, Formula.Var _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Impl p q, Formula.Impl p' q' => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2v_eq2 hl
  let r:= f2v_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.Impl _ _, Formula.And _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Impl _ _, Formula.Or _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Impl _ _, Formula.Falsum => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Impl _ _, Formula.Var _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.And p q, Formula.And p' q' => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2v_eq2 hl
  let r:= f2v_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.And _ _, Formula.Impl _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.And _ _, Formula.Or _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.And _ _, Formula.Falsum => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.And _ _, Formula.Var _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Or p q, Formula.Or p' q' => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
  intro h
  simp [fbeq]
  simp [Formula.eq]
  let hl := h.left
  let hr := h.right
  let l:= f2v_eq2 hl
  let r:= f2v_eq2 hr
  simp [fbeq] at l
  simp [fbeq] at r
  rw [l]
  rw [r]
  simp
| Formula.Or _ _, Formula.Impl _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Or _ _, Formula.And _ _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Or _ _, Formula.Falsum => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
| Formula.Or _ _, Formula.Var _ => by
  simp [translateFormulaToVarname]
  simp [Vbeq]
  simp [VarName.eq]
