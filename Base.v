Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.

Require Export List.
Export ListNotations.

Global Set Universe Polymorphism.

Definition id {A : Type} := fun x : A => x.

Notation "f .> g" := (compose g f) (at level 40).

Ltac ext x := extensionality x.

Ltac gen x := generalize dependent x.

Notation "f $ x" := (f x) (left associativity, at level 40, only parsing).

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