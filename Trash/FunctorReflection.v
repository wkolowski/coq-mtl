Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (F_inst : Functor F)
  (pure : forall A : Type, A -> F A).

Inductive type : Type :=
    | TVar : Type -> type
    | TArr : type -> type -> type
    | TF : type -> type.

Fixpoint typeDenote (t : type) : Type :=
match t with
    | TVar A => A
    | TArr t1 t2 => typeDenote t1 -> typeDenote t2
    | TF t => F (typeDenote t)
end.

Inductive Exp : type -> Type :=
    | Var : forall A : Type, A -> Exp (TVar A)
    | Id : forall A : type, Exp (TArr A A)
    | Comp :
        forall A B C : type,
          Exp (TArr A B) -> Exp (TArr B C) -> Exp (TArr A C)
    | App : forall A B : type, Exp (TArr A B) -> Exp A -> Exp B
    | Fmap : forall A B : type, Exp (TArr A B) -> Exp (TArr (TF A) (TF B)).

Arguments Var {A}.
Arguments Id {A}.
Arguments Comp {A B C}.
Arguments App {A B}.
Arguments Fmap {A B}.

Fixpoint denote {A : type} (t : Exp A) : typeDenote A :=
match t with
    | Var x => x
    | Id => id
    | Comp f g => denote f .> denote g
    | App f x => denote f (denote x)
    | Fmap f => fmap (denote f)
end.

(*
Eval cbn in denote (App (Fmap (Var (plus 2))) (Var (pure _ 42))).
*)

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Definition simplify {A : type} (e : Exp A) : Exp A.
(*
match e with
    | Var x => Var x
    | Id => Id
    | Comp e1 e2 =>
        match simplify e1 with
            | Id => simplify e2
            | e1' => Comp e1' (simplify e2)
        end
    | _ => e
end.
*)
Proof.
  induction e.
    exact (Var a).
    exact Id.
Abort.

(*
Class Reify {A : Type} (x : A) : Type :=
{
    reify : Exp A;
    denote_reify : denote reify = x
}.

Arguments reify {A} _ {Reify}.

Instance ReifyApp
  {A B C : Type} {f : A -> B} {x : A}
  (Rf : Reify f) (Rx : Reify x) : Reify (f x) | 0 :=
{
    reify := App (reify f) (reify x)
}.
Proof.
  cbn. rewrite 2!denote_reify. reflexivity.
Defined.

Instance ReifyFmap
  {A B : Type} (f : A -> B) (Rf : Reify f) : Reify (fmap f) | 0 :=
{
    reify := Fmap (reify f)
}.
Proof.
  cbn. rewrite denote_reify. reflexivity.
Defined.

Instance ReifyVar {A : Type} (x : A) : Reify x | 100 :=
{
    reify := Var x
}.
Proof.
  cbn. reflexivity.
Defined.


Eval cbn in reify f.
Eval cbn in reify x.
Eval cbn in reify (fmap f).
Eval cbn in reify (f x).
Check reify (f x).
*)

Variables
  (A B C : Type)
  (f : A -> A)
  (x y : A).

Print Exp.

Ltac reify e :=
match e with
    | id => constr:(Id)
    | ?f .> ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | compose ?f ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | ?f ?x =>
        let f' := reify f in
        let x' := reify x in constr:(App f' x')
    | fmap ?f => idtac f;
        let f' := reify f in constr:(Fmap f')
    | ?x => constr:(Var x)
(*    | _ => idtac e*)
end.

Goal 5 = 5.
Proof.
(*
  match constr:(fmap (plu
*)
  let x := reify constr:(f x) in pose x.
  let x := reify constr:(f .> f) in pose x.
Abort.