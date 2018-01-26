Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.

Definition fmap_Prod
  {A B C : Type} (f : B -> C) (x : A * B) : A * C :=
match x with
    | pair a b => pair a (f b)
end.

Hint Unfold fmap_Prod : HSLib.

Instance FunctorProd (A : Type) : Functor (prod A) :=
{
    fmap := @fmap_Prod A
}.
Proof. all: monad. Defined.

Theorem Prod_not_applicative :
  (forall A : Type, Applicative (prod A)) -> False.
Proof.
  intro. destruct (X False). destruct (ret _ tt). assumption.
Qed.