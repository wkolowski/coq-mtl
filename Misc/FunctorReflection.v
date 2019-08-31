(** This file contains an implementation of the tactic [reflect_functor],
    which does some simplification of functor-related expressions. The
    tactic is implemented using reflection, as can be seen from the name.
    However, I needed the Equations package to comfortably deal with some
    dependent pattern matching. I don't want Equations to be a dependency
    for coq-mtl, so this file is commented out until it's needed again. *)

(*
From Equations Require Import Equations.

Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (inst : Functor F).

Inductive type : Type :=
    | TVar : Set -> type
    | TArr : type -> type -> type
    | TF : type -> type.

Derive NoConfusion for type.

Fixpoint typeDenote (t : type) : Type :=
match t with
    | TVar A => A
    | TArr t1 t2 => typeDenote t1 -> typeDenote t2
    | TF t => F (typeDenote t)
end.

Inductive Exp : type -> Type :=
    | Fun : forall A B : Set, (A -> B) -> Exp (TArr (TVar A) (TVar B))
    | Id : forall A : type, Exp (TArr A A)
    | Comp :
        forall A B C : type,
          Exp (TArr A B) -> Exp (TArr B C) -> Exp (TArr A C)
    | App : forall A B : type, Exp (TArr A B) -> Exp A -> Exp B
    | Fmap : forall A B : type, Exp (TArr A B) -> Exp (TArr (TF A) (TF B)).

Arguments Fun {A B}.
Arguments Id {A}.
Arguments Comp {A B C}.
Arguments App {A B}.
Arguments Fmap {A B}.

Derive Signature NoConfusion NoConfusionHom for Exp.

Fixpoint denote {A : type} (t : Exp A) : typeDenote A :=
match t with
    | Fun f => f
    | Id => id
    | Comp f g => denote f .> denote g
    | App f x => denote f (denote x)
    | Fmap f => fmap (denote f)
end.

Inductive flist : type -> type -> Type :=
    | fnil : forall A : type, flist A A
    | fcons :
        forall A B C : type,
          Exp (TArr A B) -> flist B C -> flist A C.

Arguments fnil {A}.
Arguments fcons {A B C}.

Equations fapp
  {A B C : type} (l1 : flist A B) (l2 : flist B C) : flist A C :=
fapp fnil l2 := l2;
fapp (fcons f l1') l2 := fcons f (fapp l1' l2).
Next Obligation. Admitted.
Next Obligation. apply UIP_refl. Defined.

Equations efmap
  (f : forall A B : type,
    Exp (TArr A B) -> Exp (TArr (TF A) (TF B)))
  {A B : type} (l : flist A B) : flist (TF A) (TF B) :=
efmap f fnil := fnil;
efmap f (fcons g l') := fcons (f _ _ g) (efmap f l').

Equations flatten
  {A B : type} (e : Exp (TArr A B))
  : flist A B :=
flatten (Fun f) := fcons (Fun f) fnil;
flatten Id := fnil;
flatten (Comp e1 e2) := fapp (flatten e1) (flatten e2);
flatten (App e1 e2) := fcons (App e1 e2) fnil;
flatten (Fmap e') := efmap (@Fmap) (flatten e').

Equations flistDenote
  {A B : type} (l : flist A B) : typeDenote A -> typeDenote B :=
flistDenote fnil := id;
flistDenote (fcons f l') := denote f .> flistDenote l'.

Lemma flistDenote_fapp :
  forall (A B C : type) (l1 : flist A B) (l2 : flist B C),
    flistDenote (fapp l1 l2) = flistDenote l1 .> flistDenote l2.
Proof.
  intros. funelim (fapp l1 l2).
    simp fapp.
    simp flistDenote. rewrite H. reflexivity.
Qed.

Lemma flistDenote_efmap :
  forall
    (A B : type) (l : flist A B),
      flistDenote (efmap (@Fmap) l) = fmap (flistDenote l).
Proof.
  intros. funelim (efmap (@Fmap) l); simp flistDenote.
    rewrite fmap_id. reflexivity.
    rewrite fmap_comp, H. reflexivity.
Qed.

Lemma flistDenote_flatten :
  forall (A B : type) (e : Exp (TArr A B)),
    flistDenote (flatten e) = denote e.
Proof.
  intros. funelim (flatten e); simp flistDenote.
    rewrite flistDenote_fapp, H, H0. reflexivity.
    rewrite flistDenote_efmap, H. reflexivity.
Qed.

Lemma reflect_functor :
  forall (A B : type) (e1 e2 : Exp (TArr A B)),
    flistDenote (flatten e1) = flistDenote (flatten e2) ->
    denote e1 = denote e2.
Proof.
  intros.
  rewrite <- flistDenote_flatten, H, flistDenote_flatten.
  reflexivity.
Qed.

(*End Stuff.*)

Ltac reifyType T :=
match T with
    | ?F ?A =>
        let t := reifyType A in constr:(TF t)
    | ?A => constr:(TVar A)
end.

Ltac reify e :=
match e with
    | @id ?A =>
        let t := reifyType A in constr:(@Id t)
    | ?f .> ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | compose ?f ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | ?f ?x =>
        let f' := reify f in
        let x' := reify x in constr:(App f' x')
    | fmap ?f =>
        let f' := reify f in constr:(Fmap f')
    | ?f => constr:(Fun f)
end.

Ltac reflect_functor :=
match goal with
    | |- ?e1 = ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in
          change (denote e1' = denote e2');
          apply reflect_functor;
          repeat (simp flatten || simp efmap || simp fapp ||
                  simp flistDenote);
          cbn; rewrite !id_right
end.

Variables
  (A B C : Type)
  (f : A -> A)
  (x y : A).

Goal id .> fmap (f .> (f .> f)) = fmap (f .> f) .> id .> fmap f.
Proof.
  reflect_functor.
Qed.

Goal id .> fmap (f .> (f .> f)) = fmap (f .> f) .> id .> fmap f .> fmap f.
Proof.
  reflect_functor.
Abort.

Goal fmap f .> fmap f = fmap (f .> f).
Proof. reflect_functor. Qed.

Goal fmap id .> fmap f = fmap f.
Proof. reflect_functor. Qed.

Goal f (f x) = f (f x).
Proof.
  Fail reflect_functor.
  reflexivity.
Qed.
*)