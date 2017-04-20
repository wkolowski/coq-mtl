Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.

Definition fmap_Sum {A B C : Type} (f : B -> C) (x : sum A B) : sum A C :=
match x with
    | inl a => inl a
    | inr b => inr (f b)
end.

Instance FunctorSum (A : Type) : Functor (sum A) :=
{
    fmap := @fmap_Sum A
        
}.
Proof.
  intros. extensionality x. destruct x; unfold id; trivial.
  intros. extensionality x. destruct x; unfold id; trivial.
Defined.


