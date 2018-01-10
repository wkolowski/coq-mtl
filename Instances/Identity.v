Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Identity (A : Type) : Type := A.

Definition fmap_Identity
  {A B : Type} (f : A -> B) (a : Identity A) : Identity B := f a.

Instance FunctorIdentity : Functor Identity :=
{
    fmap := @fmap_Identity
}.
Proof. all: auto. Defined.

Definition ret_Identity {A : Type} (x : A) : Identity A := x.

Definition ap_Identity
  {A B : Type} (f : Identity A -> Identity B) (x : Identity A)
    : Identity B := f x.

Instance Applicative_Identity : Applicative Identity :=
{
    is_functor := FunctorIdentity;
    ret := @ret_Identity;
    ap := @ap_Identity
}.
Proof. all: reflexivity. Defined.

Definition bind_Identity
  {A B : Type} (a : Identity A) (f : A -> Identity B) : Identity B := f a.

Definition join_Identity
  {A : Type} (x : Identity (Identity A)) : Identity A := x.

Definition compM_Identity
  {A B C : Type} (f : A -> Identity B) (g : B -> Identity C)
  (x : A) : Identity C := g (f x).

Theorem Identity_not_Alternative :
  Alternative Identity -> False.
Proof.
  destruct 1. apply (aempty False).
Qed.