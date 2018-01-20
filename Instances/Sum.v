Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition fmap_Sum
  {E A B : Type} (f : A -> B) (x : sum E A) : sum E B :=
match x with
    | inl a => inl a
    | inr b => inr (f b)
end.

Instance FunctorSum (E : Type) : Functor (sum E) :=
{
    fmap := @fmap_Sum E
}.
Proof.
  all: intros; ext x; destruct x; compute; reflexivity.
Defined.

Definition ret_Sum {E A : Type} (x : A) : sum E A := inr x.

Definition ap_Sum
  {E A B : Type} (sf : sum E (A -> B)) (sa : sum E A) : sum E B :=
match sf, sa with
    | inl a, _ => inl a
    | _, inl a => inl a
    | inr f, inr x => inr (f x)
end.

Instance ApplicativeSum (E : Type) : Applicative (sum E) :=
{
    is_functor := FunctorSum E;
    ret := @ret_Sum E;
    ap := @ap_Sum E
}.
Proof.
  all: intros; repeat
  match goal with
      | x : _ + _ |- _ => destruct x
  end; compute; reflexivity.
Defined.

Theorem Sum_not_CommutativeApplicative :
  ~ (forall E : Type, CommutativeApplicative _ (ApplicativeSum E)).
Proof.
  intro. destruct (H bool).
  specialize (ap_comm nat nat nat (fun _ => id) (inl true) (inl false)).
  compute in ap_comm. congruence.
Qed.

Theorem Sum_not_alternative :
  (forall E : Type, Alternative (sum E)) -> False.
Proof.
  intro inst. destruct (inst False).
  destruct (aempty False); assumption. 
Qed.

Definition join_Sum {E A : Type} (ssa : sum E (sum E A)) : sum E A :=
match ssa with
    | inl e => inl e
    | inr sa =>
        match sa with
            | inl e => inl e
            | inr a => inr a
        end
end.

Definition bind_Sum
  {E A B : Type} (sa : sum E A) (f : A -> sum E B) : sum E B :=
match sa with
    | inl e => inl e
    | inr a => f a
end.

Definition compM_Sum
  {E A B C : Type} (f : A -> sum E B) (g : B -> sum E C) (x : A)
    : sum E C := bind_Sum (f x) g.