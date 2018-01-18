Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.

Require Export List.
Export ListNotations.

Global Set Universe Polymorphism.

Definition id {A : Type} := fun x : A => x.

Notation "f .> g" := (compose g f) (at level 40).

Ltac ext_aux x := extensionality x.

Tactic Notation "ext" ident(x) := extensionality x.
Tactic Notation "ext" := let x := fresh "x" in ext x.

Ltac exts := repeat ext.

(*Ltac exts'_aux l :=
match l with
    | [] => idtac
    | ?h :: ?t => ext h; exts'_aux t
end.

Tactic Notation "exts'" simple_intropattern(l) := exts'_aux l.

Goal (fun n => 1 + n) = (fun n => n + 1).
Proof.
  exts' n.*)

Ltac gen x := generalize dependent x.

Notation "f $ x" := (f x) (left associativity, at level 40, only parsing).

Lemma id_eq :
  forall (A : Type) (x : A), id x = x.
Proof. reflexivity. Qed.

Lemma id_left :
  forall (A B : Type) (f : A -> B),
    id .> f = f.
Proof.
  intros. unfold compose, id. ext x. reflexivity.
Qed.

Lemma id_right :
  forall (A B : Type) (f : A -> B),
    f .> id = f.
Proof.
  intros. unfold compose, id. ext x. reflexivity.
Qed.

Hint Rewrite @id_eq @id_left @id_right : id.

Ltac id := autorewrite with id.