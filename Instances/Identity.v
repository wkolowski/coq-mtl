Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Identity (A : Type) : Type := A.

Definition fmap_Identity {A B : Type} (f : A -> B) (ia : Identity A)
    : Identity B := f ia.

Instance FunctorIdentity : Functor Identity :=
{
    fmap := @fmap_Identity
}.
Proof. all: auto. Defined.

Definition ret_Identity {A : Type} (x : A) : Identity A := x.

Definition ap_Identity
  {A B : Type} (f : Identity A -> Identity B) (x : Identity A) : Identity B :=
    f x.

Instance Applicative_Identity : Applicative Identity :=
{
    is_functor := FunctorIdentity;
    ret := @ret_Identity;
    ap := @ap_Identity
}.
Proof. all: reflexivity. Defined.

Theorem Identity_not_Alternative :
  Alternative Identity -> False.
Proof.
  destruct 1. apply (aempty False).
Qed.