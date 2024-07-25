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
| App : Terms -> Terms -> Terms
| Pair : Terms -> Terms -> Terms
| Fst : Terms -> Terms
| Snd : Terms -> Terms
| Inl : Terms -> Types -> Types -> Terms
| Inr : Terms -> Types -> Types -> Terms
| Case : Terms -> Terms -> Terms -> Terms
| Unit : Terms
| EmptyElim : Terms ->  Terms -> Terms


def Terms.toString : Terms → String
| Terms.Var v t => v ++ " : " ++ t.toString
| Terms.Abs v t e => "λ" ++ v ++ " : " ++ t.toString ++ " . " ++ e.toString
| Terms.App e1 e2 => "(" ++ e1.toString ++ " " ++ e2.toString ++ ")"
| Terms.Pair e1 e2 => "(" ++ e1.toString ++ ", " ++ e2.toString ++ ")"
| Terms.Fst e => "fst " ++ e.toString
| Terms.Snd e => "snd " ++ e.toString
| Terms.Inl e t1 t2 => "inl " ++ e.toString ++ " as " ++ t1.toString ++ " + " ++ t2.toString
| Terms.Inr e t1 t2 => "inr " ++ e.toString ++ " as " ++ t1.toString ++ " + " ++ t2.toString
| Terms.Case e1 e2 e3 => "case " ++ e1.toString ++ " of " ++ e2.toString ++ " | " ++ e3.toString
| Terms.Unit => "()"
| Terms.EmptyElim a b => "EmptyElim " ++ a.toString ++ " as " ++ b.toString

inductive Context : Type
| Empty : Context
| Cons : String -> Types -> Context -> Context


def Context.toString : Context → String
| Context.Empty => ""
| Context.Cons x A Γ => x ++ " : " ++ A.toString ++ ", " ++ Context.toString Γ

def Context.getTypeOf : Context →  String → Option Types
| Context.Empty ,_ => none
| Context.Cons x A Γ ,y => if x = y then some A else Context.getTypeOf Γ y

def Terms.GetIsInhabitant : Context → Terms → Types → Bool
| Γ, Terms.Var x A, B => match Context.getTypeOf Γ x with
                        | some C => EqualTypes A C && EqualTypes A B
                        | none => false
| Γ, Terms.Abs x A e, Types.Arrow B C => EqualTypes A B && (Terms.GetIsInhabitant (Context.Cons x A Γ) e C || A == Types.Empty)
| Γ, Terms.App e1 e2, C => match e1 with
                          | Terms.Abs x A _ => Terms.GetIsInhabitant Γ e2 A && Terms.GetIsInhabitant (Context.Cons x A Γ) e1 (Types.Arrow A C)
                          | _ => false
| Γ, Terms.Pair e1 e2, Types.Touples A B => Terms.GetIsInhabitant Γ e1 A && Terms.GetIsInhabitant Γ e2 B
| Γ, Terms.Fst e, A => match e with
                      | Terms.Pair e1 _ => Terms.GetIsInhabitant Γ e1 A
                      | _ => false
| Γ, Terms.Snd e, B => match e with
                      | Terms.Pair _ e2 => Terms.GetIsInhabitant Γ e2 B
                      | _ => false
| Γ, Terms.Inl e A B, Types.Either C D => Terms.GetIsInhabitant Γ e A && EqualTypes A C && EqualTypes B D
| Γ, Terms.Inr e A B, Types.Either C D => Terms.GetIsInhabitant Γ e B && EqualTypes A C && EqualTypes B D
| Γ, Terms.Case e e1 e2, C => match e with
                            | Terms.Inl e' A B => Terms.GetIsInhabitant Γ e1 (Types.Arrow A C) && Terms.GetIsInhabitant Γ e2 (Types.Arrow B C) && Terms.GetIsInhabitant Γ e' A
                            | Terms.Inr e' A B => Terms.GetIsInhabitant Γ e1 (Types.Arrow A C) && Terms.GetIsInhabitant Γ e2 (Types.Arrow B C) && Terms.GetIsInhabitant Γ e' B
                            | Terms.Var x L => match Context.getTypeOf Γ x with
                                  | some (Types.Either A B) => Terms.GetIsInhabitant Γ e1 (Types.Arrow A C) && Terms.GetIsInhabitant Γ e2 (Types.Arrow B C) && L == (Types.Either A B)
                                  | _ => false
                            | _ => false
| _, Terms.Unit, Types.Unit => true
| Γ, Terms.EmptyElim e1 _, _ => Terms.GetIsInhabitant Γ e1 Types.Empty
| _, _, _ => false

-- simple example of x: A ⊢ x : A

-- def example1 : Context := Context.Cons "x" (Types.TypeVar "A") Context.Empty
-- def example1Term : Terms := Terms.Var "x" (Types.TypeVar "A")

-- #eval example1Term.toString
-- #eval Terms.GetIsInhabitant example1 example1Term (Types.TypeVar "A")

-- -- simple example of ⊢ λx:A.x : A → A

-- def example2 : Context := Context.Empty
-- def example2Term : Terms := Terms.Abs "x" (Types.TypeVar "A") (Terms.Var "x" (Types.TypeVar "A"))

-- #eval example2Term.toString
-- #eval Terms.GetIsInhabitant example2 example2Term (Types.Arrow (Types.TypeVar "A") (Types.TypeVar "A"))

-- -- simple example of "l : C, k : C, a : (A + B),  ⊢ (λx : (A + B) . case x : (A + B) of λy : A . k : C | λz : B . l : C a : (A + B)) : C"


-- def example3 : Context := Context.Empty
-- def example3Term : Terms := Terms.Abs "x"
--                                       (
--                                         Types.Either (Types.TypeVar "A") (Types.TypeVar "B")
--                                       )
--                                       (
--                                         Terms.Case (
--                                                     Terms.Var "x" (
--                                                       Types.Either (Types.TypeVar "A") (Types.TypeVar "B")
--                                                       )
--                                                     )
--                                                     (
--                                                       Terms.Abs "y"
--                                                                 (Types.TypeVar "A")
--                                                                 (Terms.Var "k" (Types.TypeVar "C"))
--                                                     )
--                                                     (
--                                                       Terms.Abs "z"
--                                                                 (Types.TypeVar "B")
--                                                                 (Terms.Var "l" (Types.TypeVar "C"))
--                                                     )
--                                       )
-- def example4 : Context := Context.Cons "l" (Types.TypeVar "C") (Context.Cons "k" (Types.TypeVar "C") (Context.Cons "a" (Types.Either (Types.TypeVar "A") (Types.TypeVar "B")) Context.Empty))
-- def example4Term : Terms := Terms.App example3Term (Terms.Var "a" (Types.Either (Types.TypeVar "A") (Types.TypeVar "B")))

-- #eval example3.toString ++ " ⊢ " ++example3Term.toString
-- #eval Terms.GetIsInhabitant example3 example3Term (Types.Arrow (Types.Either (Types.TypeVar "A") (Types.TypeVar "B")) (Types.TypeVar "C"))
-- #eval example4.toString ++ " ⊢ " ++ example4Term.toString
-- #eval Terms.GetIsInhabitant example4 example4Term (Types.TypeVar "C")

-- -- simple example of exfalso quodlibet
-- def example5 : Context := Context.Cons "a" Types.Empty Context.Empty
-- def example5Term : Terms := Terms.EmptyElim (Terms.Var "a" Types.Empty) (Terms.Var "b" (Types.TypeVar "A"))

-- #eval example5.toString ++ " ⊢ " ++ example5Term.toString
-- #eval Terms.GetIsInhabitant example5 example5Term (Types.TypeVar "A")

-- def example6 : Context := Context.Empty
-- def example6Term : Terms := Terms.Abs "x" (Types.Empty) (Terms.Var "b" (Types.TypeVar "A"))
-- #eval example6.toString ++ " ⊢ " ++ example6Term.toString
-- #eval Terms.GetIsInhabitant example6 example6Term (Types.Arrow Types.Empty (Types.TypeVar "A"))

-- -- simple example of a->b->a
-- def example7 : Context := Context.Empty
-- def example7Term : Terms := Terms.Abs "x" (Types.TypeVar "A") (Terms.Abs "y" (Types.TypeVar "B") (Terms.Var "x" (Types.TypeVar "A")))
-- #eval example7.toString ++ " ⊢ " ++ example7Term.toString
-- #eval Terms.GetIsInhabitant example7 example7Term (Types.Arrow (Types.TypeVar "A") (Types.Arrow (Types.TypeVar "B") (Types.TypeVar "A")))

-- -- simple example of a->a
-- def example8 : Context := Context.Empty
-- def example8Term : Terms := Terms.Abs "x" (Types.TypeVar "A") (Terms.Var "x" (Types.TypeVar "A"))
-- #eval example8.toString ++ " ⊢ " ++ example8Term.toString
-- #eval Terms.GetIsInhabitant example8 example8Term (Types.Arrow (Types.TypeVar "A") (Types.TypeVar "A"))

-- -- simple example of a->b fail cause b is not habitet
-- def example9 : Context := Context.Empty
-- def example9Term : Terms := Terms.Abs "x" (Types.TypeVar "A") (Terms.Var "x" (Types.TypeVar "B"))
-- #eval example9.toString ++ " ⊢ " ++ example9Term.toString
-- #eval Terms.GetIsInhabitant example9 example9Term (Types.Arrow (Types.TypeVar "A") (Types.TypeVar "B"))
