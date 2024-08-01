import CurryHowardCorrespondence.Varset

inductive Types : Type
| TypeVar : typeVarNames → Types
| Arrow : Types → Types → Types
| Touples : Types → Types → Types
| Either : Types → Types → Types
| Empty : Types

def EqualTypes : Types → Types → Bool
| Types.TypeVar v1, Types.TypeVar v2 => v1 == v2
| Types.Arrow t1 t2, Types.Arrow t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Touples t1 t2, Types.Touples t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Either t1 t2, Types.Either t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Empty, Types.Empty => true
| _, _ => false

instance : BEq Types := ⟨EqualTypes⟩

def Types.toString : Types → String
| Types.TypeVar v => v.toString
| Types.Arrow t1 t2 => "(" ++ t1.toString ++ " → " ++ t2.toString ++ ")"
| Types.Touples t1 t2 => "(" ++ t1.toString ++ " × " ++ t2.toString ++ ")"
| Types.Either t1 t2 => "(" ++ t1.toString ++ " + " ++ t2.toString ++ ")"
| Types.Empty => "⊥"

inductive Term : Type
| Var : termVarNames → Term
| Abs : termVarNames → Types → Term → Term
| App : Term → Term → Term
| Pair : Term → Term → Term
| Proj1 : Term → Term
| Proj2 : Term → Term
| Inl : Term → Types → Types → Term
| Inr : Term → Types → Types → Term
| Case : Term → termVarNames → Term → termVarNames → Term → Term
| Absurd : Types → Term → Term -- absurdity elimination

def Term.eq : Term → Term → Bool
| Term.Var x, Term.Var x' => x==x'
| Term.Abs x t T, Term.Abs x' t' T' => x==x' && t==t' && eq T T'
| Term.App T1 T2, Term.App T1' T2' => eq T1 T1' && eq T2 T2'
| Term.Pair T1 T2, Term.Pair T1' T2' => eq T1 T1' && eq T2 T2'
| Term.Proj1 T1, Term.Proj1 T1' => eq T1 T1'
| Term.Proj2 T1, Term.Proj2 T1' => eq T1 T1'
| Term.Inl T1 t1 t2 , Term.Inl T1' t1' t2' => eq T1 T1' && t1==t1' && t2==t2'
| Term.Case T x1 T1 x2 T2, Term.Case T' x1' T1' x2' T2' => eq T T' && eq T1 T1' && eq T2 T2' && x1 == x1' && x2 == x2'
| Term.Absurd t T, Term.Absurd t' T' => eq T T' && t == t'
| _, _ => false

instance: BEq Term := ⟨Term.eq⟩

inductive Context : Type
| Empty : Context
| Cons : Term -> Types -> Context -> Context


def Context.getType : Context → Term → Option Types
| Empty ,_ => none
| Cons x t Γ , y => if x == y then some t else getType Γ y

def Context.IsSub: Context → Context → Bool
| Empty, _ => true
| Cons x t Γ, Γ' => Context.getType Γ x == some t && IsSub Γ Γ'

def Context.concat : Context → Context → Context
| Empty, Γ => Γ
| Cons x t Γ, Γ' => Cons x t (concat Γ Γ')

def Context.BEq : Context → Context → Bool := λ Γ Γ' => Context.IsSub Γ Γ' && Context.IsSub Γ' Γ

instance : BEq Context := ⟨Context.BEq⟩


inductive Inhabitable : Context → Types → Term → Prop
| Var {Γ x A} (h : Γ.getType x = some A) : Inhabitable Γ A x
| Abs {Γ x A B t} (h : Inhabitable (Context.Cons (Term.Var x) A Γ) B t) : Inhabitable Γ (Types.Arrow A B) (Term.Abs x A t)
| App {Γ A B t1 t2} (h1 : Inhabitable Γ (Types.Arrow A B) t1) (h2 : Inhabitable Γ A t2) : Inhabitable Γ B (Term.App t1 t2)
| Pair {Γ A B t1 t2} (h1 : Inhabitable Γ A t1) (h2 : Inhabitable Γ B t2) : Inhabitable Γ (Types.Touples A B) (Term.Pair t1 t2)
| Proj1 {Γ A B t} (h : Inhabitable Γ (Types.Touples A B) t) : Inhabitable Γ A (Term.Proj1 t)
| Proj2 {Γ A B t} (h : Inhabitable Γ (Types.Touples A B) t) : Inhabitable Γ B (Term.Proj2 t)
| Inl {Γ A B t} (h : Inhabitable Γ A t) : Inhabitable Γ (Types.Either A B) (Term.Inl t A B)
| Inr {Γ A B t} (h : Inhabitable Γ B t) : Inhabitable Γ (Types.Either A B) (Term.Inr t A B)
| Case {Γ A B C t t1 t2 x y} (h1 : Inhabitable Γ (Types.Either A B) t) (h2 : Inhabitable (Context.Cons (Term.Var x) A Γ) C t1) (h3 : Inhabitable (Context.Cons (Term.Var y) B Γ) C t2) : Inhabitable Γ C (Term.Case t x t1 y t2)
| Absurd {Γ A t} (h : Inhabitable Γ Types.Empty t) : Inhabitable Γ A (Term.Absurd A t)
