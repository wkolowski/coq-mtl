Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

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

Definition ret_Sum {A B : Type} (b : B) : sum A B := inr b.

Definition ap_Sum {A B C : Type} (sf : sum A (B -> C)) (sx : sum A B)
    : sum A C :=
match sf, sx with
    | inl a, _ => inl a
    | _, inl a => inl a
    | inr f, inr x => inr (f x)
end.

Instance ApplicativeSum (A : Type) : Applicative (sum A) :=
{
    is_functor := FunctorSum A;
    ret := @ret_Sum A;
    ap := @ap_Sum A
}.
Proof.
  destruct ax. simpl. trivial.
  simpl. unfold id. trivial.
  destruct af, ag, ax; simpl; trivial.
  intros. simpl. unfold ret_Sum. trivial.
  destruct f; simpl; trivial.
Defined.

Theorem Sum_not_alternative : exists A : Type,
    Alternative (sum A) -> False.
Proof.
  exists False. destruct 1. destruct (aempty False); assumption.
Qed.

Definition join_Sum {A B : Type} (x : sum A (sum A B)) : sum A B :=
match x with
    | inl a => inl a
    | inr x' =>
        match x' with
            | inl a => inl a
            | inr b => inr b
        end
end.

Definition bind_Sum {A B C : Type} (x : sum A B) (f : B -> sum A C)
    : sum A C :=
match x with
    | inl a => inl a
    | inr b => f b
end.

Definition compM_Sum {E A B C : Type} (f : A -> sum E B) (g : B -> sum E C)
    (x : A) : sum E C := bind_Sum (f x) g.