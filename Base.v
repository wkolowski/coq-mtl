Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.
(*Require Export Arith.*)
Require Export List.
Export ListNotations.

Definition id {A : Type} := fun x : A => x.

Notation "f .> g" := (compose g f) (at level 40).