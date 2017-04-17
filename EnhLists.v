Require Import Monoid.

Inductive EList (A : Monoid) : A -> Type :=
    | enil : EList A neutr
    | econs : forall h s : A, EList A s -> EList A (op h s).

Arguments enil [A].
Arguments econs [A] _ [s] _.

Print econs.

Definition get {A : Monoid} {s : A} (ela : EList A s) : A := s.



Inductive ListF (A : Set) (f : A -> A -> A) : A -> Set :=
    | nil_F : forall a : A, ListF A f a
    | cons_F : forall acc : A,
        forall a : A, ListF A f acc -> ListF A f (f a acc).

Print nil_F.

Arguments nil_F [A] _ _.
Arguments cons_F [A] [f] [acc] _ _.

Definition extract {A : Set} {f : A -> A -> A} {a : A} (l : ListF A f a) := a.

Eval compute in extract (cons_F 6 (nil_F max 5)).
