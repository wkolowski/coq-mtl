Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.

Definition fmap_Prod {A B C : Type} (f : B -> C) (x : A * B) : A * C :=
match x with
    | pair a b => pair a (f b)
end.

Instance FunctorProd (A : Type) : Functor (prod A) :=
{
    fmap := @fmap_Prod A
}.
Proof.
  intros. extensionality x. destruct x; unfold id; trivial.
  intros. extensionality x. destruct x; unfold id; trivial.
Defined.

Theorem Prod_not_applicative : exists A : Type,
    Applicative (prod A) -> False.
Proof.
  exists False. destruct 1. destruct (ret _ 42). assumption.
Qed.



