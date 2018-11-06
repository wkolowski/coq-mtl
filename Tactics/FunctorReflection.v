Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (F_inst : Functor F)
  (pure : forall A : Type, A -> F A).

Inductive FExp : Type -> Type :=
    | Var : forall A : Type, A -> FExp A
    | Id : forall A : Type, FExp (A -> A)
    | Comp :
        forall A B C : Type, FExp (A -> B) -> FExp (B -> C) -> FExp (A -> C)
    | App : forall A B : Type, FExp (A -> B) -> FExp A -> FExp B
    | Fmap : forall A B : Type, FExp (A -> B) -> FExp (F A -> F B).

Arguments Var {A}.
Arguments Id {A}.
Arguments Comp {A B C}.
Arguments App {A B}.
Arguments Fmap {A B}.

Fixpoint denote {A : Type} (t : FExp A) : A :=
match t with
    | Var x => x
    | Id => id
    | Comp f g => denote f .> denote g
    | App f x => denote f (denote x)
    | Fmap f => fmap (denote f)
end.

Eval cbn in denote (App (Fmap (Var (plus 2))) (Var (pure _ 42))).

Require Import Coq.Logic.JMeq.

(*
Program Fixpoint simplify {A : Type} (e : FExp A) : FExp A :=
match e with
    | Var x => Var x
    | Id => Id
    | Comp e1 e2 =>
        match simplify e1 with
            | Id => simplify e2
            | _ => Comp e1 e2
        end
end.
            | e1', Id => e1'
            | e1', e2' => Comp e1' e2'
        end
    | _ => e
end.
Proof.
  induction e.
    exact (Var a).
    exact Id.
    inv IHe1.
      Focus 2. 
Qed.
*)

(*
Class Reify {A : Type} (x : A) : Type :=
{
    reify : FExp A;
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

Print FExp.

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