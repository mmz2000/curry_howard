inductive Types : Type
| TypeVar : String → Types
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
| Types.TypeVar v => v
| Types.Arrow t1 t2 => "(" ++ t1.toString ++ " → " ++ t2.toString ++ ")"
| Types.Touples t1 t2 => "(" ++ t1.toString ++ " × " ++ t2.toString ++ ")"
| Types.Either t1 t2 => "(" ++ t1.toString ++ " + " ++ t2.toString ++ ")"
| Types.Empty => "⊥"

inductive Context : Type
| Empty : Context
| Cons : String -> Types -> Context -> Context


def Context.toString : Context → String
| Context.Empty => ""
| Context.Cons x A Γ => x ++ " : " ++ A.toString ++ ", " ++ Context.toString Γ

def Context.getType : Context → String → Option Types
| Empty ,_ => none
| Cons x t Γ , y => if x == y then some t else getType Γ y

inductive Term : Type
| Var : String → Types → Term
| Abs : String → Types → Term → Term
| App : Term → Term → Term
| Pair : Term → Term → Term
| Proj1 : Term → Term
| Proj2 : Term → Term
| Inl : Term → Types → Types → Term
| Inr : Term → Types → Types → Term
| Case : Term → String → Term → String → Term → Term
| Absurd : Types → Term → Term -- absurdity elimination


inductive Inhabitable : Context → Types → Term → Prop
| Var {Γ x A} (h : Γ.getType x = some A) : Inhabitable Γ A (Term.Var x A)
| Abs {Γ x A B t} (h : Inhabitable (Context.Cons x A Γ) B t) : Inhabitable Γ (Types.Arrow A B) (Term.Abs x A t)
| App {Γ A B t1 t2} (h1 : Inhabitable Γ (Types.Arrow A B) t1) (h2 : Inhabitable Γ A t2) : Inhabitable Γ B (Term.App t1 t2)
| Pair {Γ A B t1 t2} (h1 : Inhabitable Γ A t1) (h2 : Inhabitable Γ B t2) : Inhabitable Γ (Types.Touples A B) (Term.Pair t1 t2)
| Proj1 {Γ A B t} (h : Inhabitable Γ (Types.Touples A B) t) : Inhabitable Γ A (Term.Proj1 t)
| Proj2 {Γ A B t} (h : Inhabitable Γ (Types.Touples A B) t) : Inhabitable Γ B (Term.Proj2 t)
| Inl {Γ A B t} (h : Inhabitable Γ A t) : Inhabitable Γ (Types.Either A B) (Term.Inl t A B)
| Inr {Γ A B t} (h : Inhabitable Γ B t) : Inhabitable Γ (Types.Either A B) (Term.Inr t A B)
| Case {Γ A B C t t1 t2 x y} (h1 : Inhabitable Γ (Types.Either A B) t) (h2 : Inhabitable (Context.Cons x A Γ) C t1) (h3 : Inhabitable (Context.Cons y B Γ) C t2) : Inhabitable Γ C (Term.Case t x t1 y t2)
| Absurd {Γ A t} (h : Inhabitable Γ Types.Empty t) : Inhabitable Γ A (Term.Absurd A t)
