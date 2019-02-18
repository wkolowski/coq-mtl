From Equations Require Import Equations.

Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (F_inst : Functor F)
  (pure : forall A : Type, A -> F A).

Polymorphic Cumulative Inductive type : Type :=
    | TVar : Set -> type
    | TArr : type -> type -> type
    | TF : type -> type.

Fixpoint typeDenote (t : type) : Type :=
match t with
    | TVar A => A
    | TArr t1 t2 => typeDenote t1 -> typeDenote t2
    | TF t => F (typeDenote t)
end.

Inductive Exp : type -> Type :=
    | Var : forall A : Set, A -> Exp (TVar A)
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

Check @NoConfusion.
Print NoConfusionPackage.

Derive NoConfusion for type.
Derive Signature NoConfusion NoConfusionHom for Exp.

Equations simplify {t : type} (e : Exp t) : Exp t :=
simplify (Var x) := Var x ;
simplify Id := Id;
simplify (Comp e1 e2) with simplify e1 => {
  simplify (Comp e1 e2) Id := simplify e2;
  simplify (Comp e1 e2) e1' := Comp e1' (simplify e2) };
simplify (App e1 e2) with simplify e1 => {
  simplify (App e1 e2) Id := simplify e2;
  simplify (App e1 e2) e1' := App e1' (simplify e2) };
simplify (Fmap e') with simplify e' => {
  simplify (Fmap e') Id := Id;
  simplify (Fmap e') e'' := Fmap e''}.

Lemma denote_simplify :
  forall (t : type) (e : Exp t),
    denote (simplify e) = denote e.
Proof.
  intros.
  funelim (simplify e); cbn;
  rewrite ?H, <- ?Hind, ?Heq; cbn; try reflexivity.
  rewrite fmap_id. reflexivity.
Qed.

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

(*
Goal 5 = 5.
Proof.
(*
  match constr:(fmap (plu
*)
  let x := reify constr:(f x) in pose x.
  let f := constr:(Comp (Var f) (Var f)) in pose f.
  let x := reify constr:(f .> f) in pose x.
Abort.
*)