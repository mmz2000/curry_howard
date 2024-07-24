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
| Subs : Terms -> Terms -> Terms -> Terms
| Unit : Terms
| Empty : Terms


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
| Terms.Subs e1 e2 e3 => e1.toString ++ "[" ++ e2.toString ++ " := " ++ e3.toString ++ "]"
| Terms.Unit => "()"
| Terms.Empty => "⊥"

inductive Context : Type
| Empty : Context
| Cons : String -> Types -> Context -> Context

inductive Judgement : Context → Terms → Types → Type
| Var : ∀ {Γ : Context} {x : String} {A : Types}, Context → Terms → Types →  Judgement Γ (Terms.Var x A) A
| Abs : ∀ {Γ : Context} {x : String} {A : Types} {e : Terms} {B : Types}, Judgement (Context.Cons x A Γ) e B → Judgement Γ (Terms.Abs x A e) (Types.Arrow A B)
| App : ∀ {Γ : Context} {e1 e2 : Terms} {A B : Types}, Judgement Γ e1 (Types.Arrow A B) → Judgement Γ e2 A → Judgement Γ (Terms.App e1 e2) B
| Pair : ∀ {Γ : Context} {e1 e2 : Terms} {A B : Types}, Judgement Γ e1 A → Judgement Γ e2 B → Judgement Γ (Terms.Pair e1 e2) (Types.Touples A B)
| Fst : ∀ {Γ : Context} {e : Terms} {A B : Types}, Judgement Γ e (Types.Touples A B) → Judgement Γ (Terms.Fst e) A
| Snd : ∀ {Γ : Context} {e : Terms} {A B : Types}, Judgement Γ e (Types.Touples A B) → Judgement Γ (Terms.Snd e) B
| Inl : ∀ {Γ : Context} {e : Terms} {A B : Types}, Judgement Γ e A → Judgement Γ (Terms.Inl e A B) (Types.Either A B)
| Inr : ∀ {Γ : Context} {e : Terms} {A B : Types}, Judgement Γ e B → Judgement Γ (Terms.Inr e A B) (Types.Either A B)
| Case : ∀ {Γ : Context} {e e1 e2 : Terms} {A B C : Types}, Judgement Γ e (Types.Either A B) → Judgement Γ e1 (Types.Arrow A C) → Judgement Γ e2 (Types.Arrow B C) → Judgement Γ (Terms.Case e e1 e2) C
| Unit : ∀ {Γ : Context}, Judgement Γ Terms.Unit Types.Unit
| EmptyElim : ∀ {Γ : Context} {e : Terms}, Judgement Γ e Types.Empty → Judgement Γ (Terms.Empty) A


def Context.toString : Context → String
| Context.Empty => ""
| Context.Cons x A Γ => x ++ " : " ++ A.toString ++ ", " ++ Context.toString Γ

def Context.getTypeOf : Context →  String → Option Types
| Context.Empty ,_ => none
| Context.Cons x A Γ ,y => if x = y then some A else Context.getTypeOf Γ y

def Judgement.toString : ∀ {Γ : Context} {e : Terms} {A : Types}, Judgement Γ e A → String
| Γ ,Terms.Var x A ,_ ,Judgement.Var _ _ _=>Γ.toString ++ Γ.toString ++ x ++ " : " ++ A.toString
| Γ ,Terms.Abs x A _ ,_ ,Judgement.Abs proof =>Γ.toString ++ "λ" ++ x ++ " : " ++ A.toString ++ " . " ++ proof.toString
| Γ ,Terms.App _ _ ,_ ,Judgement.App proof1 proof2 =>Γ.toString ++ "(" ++ proof1.toString ++ " " ++ proof2.toString ++ ")"
| Γ ,Terms.Pair _ _ ,_ ,Judgement.Pair proof1 proof2 =>Γ.toString ++ "(" ++ proof1.toString ++ ", " ++ proof2.toString ++ ")"
| Γ ,Terms.Fst _ ,_ ,Judgement.Fst proof =>Γ.toString ++ "fst " ++ proof.toString
| Γ ,Terms.Snd _ ,_ ,Judgement.Snd proof =>Γ.toString ++ "snd " ++ proof.toString
| Γ ,Terms.Inl _ A B ,_ ,Judgement.Inl proof =>Γ.toString ++ "inl " ++ proof.toString ++ " as " ++ A.toString ++ " + " ++ B.toString
| Γ ,Terms.Inr _ A B ,_ ,Judgement.Inr proof =>Γ.toString ++ "inr " ++ proof.toString ++ " as " ++ A.toString ++ " + " ++ B.toString
| Γ ,Terms.Case _ _ _ ,_ ,Judgement.Case proof1 proof2 proof3 =>Γ.toString ++ "case " ++ proof1.toString ++ " of " ++ proof2.toString ++ " | " ++ proof3.toString
| Γ ,Terms.Unit ,_ ,Judgement.Unit =>Γ.toString ++ "()"
| Γ ,Terms.Empty ,_ ,Judgement.EmptyElim proof =>Γ.toString ++ proof.toString

def getTypeOfTerm : Terms →  Option Types
| Terms.Var _ A => A
| Terms.Abs _ A e => match getTypeOfTerm e with
                      | some B => some (Types.Arrow A B)
                      | none => none
| Terms.App e1 e2 => match getTypeOfTerm e1, getTypeOfTerm e2 with
                      | some (Types.Arrow A B), some C => if A == C then some B else none
                      | _,_ => none
| Terms.Pair e1 e2 => match getTypeOfTerm e1, getTypeOfTerm e2 with
                      | some A, some B => some (Types.Touples A B)
                      | _,_ => none
| Terms.Fst e => match getTypeOfTerm e with
                  | some (Types.Touples A _) => some A
                  | _ => none
| Terms.Snd e => match getTypeOfTerm e with
                  | some (Types.Touples _ B) => some B
                  | _ => none
| Terms.Inl e _ B => match getTypeOfTerm e with
                      | some A => some (Types.Either A B)
                      | _ => none
| Terms.Inr e A _ => match getTypeOfTerm e with
                      | some B => some (Types.Either A B)
                      | _ => none
| Terms.Case e e1 e2 => match getTypeOfTerm e with
                        | some (Types.Either A B) => match getTypeOfTerm e1, getTypeOfTerm e2 with
                                                      | some (Types.Arrow K C), some (Types.Arrow J D) => if C == D && (
                                                        (A==K && B==J )|| (A==J && B==K)
                                                      ) then some C else none
                                                      | _,_ => none
                        | _ => none
| Terms.Unit => some Types.Unit
| Terms.Empty => none
| Terms.Subs e1 e2 e3 => if getTypeOfTerm e2 == getTypeOfTerm e3 then getTypeOfTerm e1 else none


def CheckJudgement : Judgement Γ T t →  Bool
| Judgement.Var Γ T t => match Γ.getTypeOf T.toString with
                      | some j =>  j == t
                      | none => False
| Judgement.Abs T => CheckJudgement T
| Judgement.App T1 T2 => CheckJudgement T1 && CheckJudgement T2
| Judgement.Pair T1 T2 => CheckJudgement T1 && CheckJudgement T2
| Judgement.Fst T => CheckJudgement T
| Judgement.Snd T => CheckJudgement T
| Judgement.Inl T => CheckJudgement T
| Judgement.Inr T => CheckJudgement T
| Judgement.Case T1 T2 T3 => CheckJudgement T1 && CheckJudgement T2 && CheckJudgement T3
| Judgement.Unit => true
| Judgement.EmptyElim T => !CheckJudgement T
