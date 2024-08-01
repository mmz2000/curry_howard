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
