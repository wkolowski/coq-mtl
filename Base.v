Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.

Require Export List.
Export ListNotations.

Global Set Universe Polymorphism.

Definition id {A : Type} := fun x : A => x.

Notation "f .> g" := (compose g f) (at level 40).