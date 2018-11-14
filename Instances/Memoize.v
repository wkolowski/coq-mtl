Require Import Control.

Set Universe Polymorphism.

(*
Inductive Memoize : Type -> Type :=
    | Pure : forall A : Type, A -> Memoize A
    | Call : forall A B : Type, (A -> B) -> A -> Memoize B
    | Bind : forall A B : Type, Memoize A -> (A -> Memoize B) -> Memoize B.
*)

Inductive Memoize (A : Type) : Type :=
    | Pure : A -> Memoize A
    | Call : forall B : Type, (B -> Memoize A) -> B -> Memoize A
    | Bind : forall B : Type, Memoize B -> (B -> Memoize A) -> Memoize A.

Arguments Pure {A}.
Arguments Call {A B}.
Arguments Bind {A B}.


Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).
Notation "'do' e" := e.

Fixpoint fib (n : nat) : Memoize nat :=
match n with
    | 0 => Pure 0
    | 1 => Pure 1
    | S (S n2 as n1) =>
        Bind (fib n2) (fun r2 : nat =>
        Bind (fib n1) (fun r1 : nat => Pure (r2 + r1)))
end.

Fixpoint extract {A : Type} (x : Memoize A) : A :=
match x with
    | Pure a => a
    | Call f x => extract (f x)
    | Bind x f => extract (f (extract x))
end.

Compute extract (fib 23).

Definition fibF (self : nat -> Memoize nat) (n : nat) : Memoize nat :=
match n with
    | 0 => Pure 0
    | 1 => Pure 1
    | S (S n2 as n1) =>
        Bind (Call self n2) (fun r2 : nat =>
        Bind (Call self n1) (fun r1 : nat => Pure (r2 + r1)))
end.


(*
Fixpoint fmap_Memoize
  {A B : Type} (f : A -> B) (x : Memoize A) : Memoize B. (*
match x with
    | Pure a => Pure (f a)
    | Call g y => Pure (f (g y))
    | Bind y g => Bind y (fun a : A => fmap_Memoize _ _ (f (g a)))
end.*)
Proof.
  destruct x.
    exact (Pure (f a)).
    exact (Call (b .> f) b).
    apply (Bind x (fun x : B0 => fmap_Memoize _ _ f (m x))).
Defined.

Instance Functor_Memoize : Functor Memoize :=
{
    fmap := @fmap_Memoize;
}.
Proof.
  intros. ext x. induction x; cbn.
    reflexivity.
    reflexivity.
    unfold id. f_equal. ext a. apply H.
  intros. ext x. induction x; cbn.
    1-2: reflexivity.
    f_equal. ext a. apply H.
Defined.

Definition pure_Memoize {A : Type} (x : A) : Memoize A := Pure x.

Definition ap_Memoize
  {A B : Type} (f : Memoize (A -> B)) (x : Memoize A) : Memoize B :=
    Bind f (fun f : A -> B => Bind x (fun x : A => Call f x)).

Instance Applicative_Memoize : Applicative Memoize :=
{
    is_functor := @Functor_Memoize;
}.
*)