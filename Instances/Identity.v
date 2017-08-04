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
Proof. auto. auto. Defined.