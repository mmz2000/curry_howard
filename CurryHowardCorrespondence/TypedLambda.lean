inductive Types : Type
| TypeVar : String → Types
| Arrow : Types → Types → Types
| Touples : Types → Types → Types
| Either : Types → Types → Types
| Unit : Types
| Empty : Types

def EqualTypes : Types → Types → Bool
| Types.TypeVar v1, Types.TypeVar v2 => v1 == v2
| Types.Arrow t1 t2, Types.Arrow t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Touples t1 t2, Types.Touples t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Either t1 t2, Types.Either t3 t4 => EqualTypes t1 t3 && EqualTypes t2 t4
| Types.Unit, Types.Unit => true
| Types.Empty, Types.Empty => true
| _, _ => false

instance : BEq Types := ⟨EqualTypes⟩

def Types.toString : Types → String
| Types.TypeVar v => v
| Types.Arrow t1 t2 => "(" ++ t1.toString ++ " → " ++ t2.toString ++ ")"
| Types.Touples t1 t2 => "(" ++ t1.toString ++ " × " ++ t2.toString ++ ")"
| Types.Either t1 t2 => "(" ++ t1.toString ++ " + " ++ t2.toString ++ ")"
| Types.Unit => "()"
| Types.Empty => "⊥"

inductive Terms : Type
| Var : String -> Types -> Terms
| Abs : String -> Types -> Terms -> Terms
| App : Types -> Terms -> Terms -> Terms
| Pair : Types -> Terms -> Terms -> Terms
| Fst : Types -> Terms -> Terms
| Snd : Types -> Terms -> Terms
| Inl : Terms -> Types -> Types -> Terms
| Inr : Terms -> Types -> Types -> Terms
| Case : Types-> Terms -> Terms -> Terms -> Terms
| Unit : Terms
| EmptyElim : Types -> Terms ->  Terms -> Terms


def Terms.toString : Terms → String
| Terms.Var v t => v ++ " : " ++ t.toString
| Terms.Abs v t e => "λ" ++ v ++ " : " ++ t.toString ++ " . " ++ e.toString
| Terms.App t e1 e2 => "(" ++ e1.toString ++ ")" ++ e2.toString ++ " : " ++ t.toString
| Terms.Pair t e1 e2 => "(" ++ e1.toString ++ ", " ++ e2.toString ++ ")" ++ " : " ++ t.toString
| Terms.Fst t e => "fst " ++ e.toString  ++ " : " ++ t.toString
| Terms.Snd t e => "snd " ++ e.toString ++ " : " ++ t.toString
| Terms.Inl e t1 t2 => "inl " ++ e.toString ++ " as " ++ t1.toString ++ " + " ++ t2.toString
| Terms.Inr e t1 t2 => "inr " ++ e.toString ++ " as " ++ t1.toString ++ " + " ++ t2.toString
| Terms.Case t e1 e2 e3 => "case " ++ e1.toString ++ " of " ++ e2.toString ++ " | " ++ e3.toString ++ " : " ++ t.toString
| Terms.Unit => "()"
| Terms.EmptyElim t a b => "EmptyElim " ++ a.toString ++ " as " ++ b.toString ++ " : " ++ t.toString

inductive Context : Type
| Empty : Context
| Cons : String -> Types -> Context -> Context


def Context.toString : Context → String
| Context.Empty => ""
| Context.Cons x A Γ => x ++ " : " ++ A.toString ++ ", " ++ Context.toString Γ

def Context.getTypeOf : Context →  String → Option Types
| Context.Empty ,_ => none
| Context.Cons x A Γ ,y => if x = y then some A else Context.getTypeOf Γ y

def Terms.getTypeOf : Context → Terms → Types
| Γ, Terms.Var x A => match Context.getTypeOf Γ x with
                        | some B => if B == A then A else Types.Empty
                        | none => Types.Empty
| Γ, Terms.Abs x A e => match Terms.getTypeOf (Context.Cons x A Γ) e with
                        | B =>  (Types.Arrow A B)
| Γ, Terms.App _ e1 e2 => match Terms.getTypeOf Γ e1 with
                          | Types.Arrow A B => if Terms.getTypeOf Γ e2 == some A then B else Types.Empty
                          | _ => Types.Empty
| Γ, Terms.Pair t e1 e2 => match t with
                          | Types.Touples A B => if Terms.getTypeOf Γ e1 == some A && Terms.getTypeOf Γ e2 == some B then t else Types.Empty
                          | _ => Types.Empty
| Γ, Terms.Fst _ e => match Terms.getTypeOf Γ e with
                          | (Types.Touples A _) => A
                          | _ => Types.Empty
| Γ, Terms.Snd _ e => match Terms.getTypeOf Γ e with
                          | (Types.Touples _ B) => B
                          | _ => Types.Empty
| Γ, Terms.Inl e A B => if Terms.getTypeOf Γ e == A then (Types.Either A B) else Types.Empty
| Γ, Terms.Inr e A B => if Terms.getTypeOf Γ e == B then  (Types.Either A B) else Types.Empty
| Γ, Terms.Case t e e1 e2 => match Terms.getTypeOf Γ e with
                            |  (Types.Either A B) => if Terms.getTypeOf Γ e1 == some (Types.Arrow A t) && Terms.getTypeOf Γ e2 == some (Types.Arrow B t) then  t else Types.Empty
                            | _ => Types.Empty
| _, Terms.Unit =>  Types.Unit
| Γ, Terms.EmptyElim t e1 e2 => if Terms.getTypeOf Γ e1 == Types.Empty && Terms.getTypeOf Γ e2 == some t then t else Types.Empty

def Terms.GetIsInhabitant : Context → Terms → Types → Bool
| Γ, Terms.Var x A, B => match Context.getTypeOf Γ x with
                        | some C => EqualTypes A C && EqualTypes A B
                        | none => B == Types.Empty
| Γ, Terms.Abs x A e, Types.Arrow B C => EqualTypes A B && (Terms.GetIsInhabitant (Context.Cons x A Γ) e C || A == Types.Empty)
| Γ, Terms.App t e1 e2, C => match Terms.getTypeOf Γ e1 with
                          | Types.Arrow A B => Terms.GetIsInhabitant Γ e1 (Types.Arrow A B) && Terms.GetIsInhabitant Γ e2 A && EqualTypes B C && EqualTypes t C
                          | _ => C == Types.Empty
| Γ, Terms.Pair t e1 e2, Types.Touples A B => Terms.GetIsInhabitant Γ e1 A && Terms.GetIsInhabitant Γ e2 B && EqualTypes t (Types.Touples A B)
| Γ, Terms.Fst t e, A => match Terms.getTypeOf Γ e with
                          | Types.Touples B C => Terms.GetIsInhabitant Γ e (Types.Touples B C) && EqualTypes A B && EqualTypes t A
                          | _ => A == Types.Empty
| Γ, Terms.Snd t e, B => match Terms.getTypeOf Γ e with
                          | Types.Touples A C => Terms.GetIsInhabitant Γ e (Types.Touples A C) && EqualTypes B C && EqualTypes t B
                          | _ => B == Types.Empty
| Γ, Terms.Inl e A B, Types.Either C D => Terms.GetIsInhabitant Γ e A && EqualTypes A C && EqualTypes B D
| Γ, Terms.Inr e A B, Types.Either C D => Terms.GetIsInhabitant Γ e B && EqualTypes A C && EqualTypes B D
| Γ, Terms.Case t e e1 e2, C => match Terms.getTypeOf Γ e with
                            |  (Types.Either A B) => Terms.GetIsInhabitant Γ e (Types.Either A B) && Terms.GetIsInhabitant Γ e1 (Types.Arrow A t) && Terms.GetIsInhabitant Γ e2 (Types.Arrow B t) && EqualTypes t C
                            | _ => C == Types.Empty
| _, Terms.Unit, Types.Unit => true
| Γ, Terms.EmptyElim t e1 b, c => Terms.GetIsInhabitant Γ e1 Types.Empty && Terms.GetIsInhabitant Γ b c && EqualTypes t c
| _, _, t => t == Types.Empty
