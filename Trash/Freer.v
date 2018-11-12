Require Import Control.

Inductive Freer (F : Type -> Type) (A : Type) : Type :=
    | Pure : A -> Freer F A
    | Bind : F A -> (A -> Freer F A) -> Freer F A.

Fixpoint bind_Freer
  {F : Type -> Type} {A B : Type} (x : Freer A) (f : A -> Freer B) : Freer B :=
match x with
    | Pure a => f a
    | Bind fa g => 

Fixpoint fmap_Freer
  {F : Type -> Type} {A B : Type} (f : A -> B) (x : Freer A) : Freer B :=
match x with
    | Pure a => Pure (f a)
    | Bind fa g => 