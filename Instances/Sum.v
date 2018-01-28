Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.Foldable.

Definition Sum (E A : Type) : Type := sum E A.

Definition fmap_Sum
  {E A B : Type} (f : A -> B) (x : sum E A) : sum E B :=
match x with
    | inl a => inl a
    | inr b => inr (f b)
end.

Hint Unfold Sum fmap_Sum : HSLib.

Instance FunctorSum (E : Type) : Functor (sum E) :=
{
    fmap := @fmap_Sum E
}.
Proof. all: monad. Defined.

Definition pure_Sum {E A : Type} (x : A) : sum E A := inr x.

Definition ap_Sum
  {E A B : Type} (sf : sum E (A -> B)) (sa : sum E A) : sum E B :=
match sf, sa with
    | inl a, _ => inl a
    | _, inl a => inl a
    | inr f, inr x => inr (f x)
end.

Hint Unfold pure_Sum ap_Sum : HSLib.

Instance ApplicativeSum (E : Type) : Applicative (sum E) :=
{
    is_functor := FunctorSum E;
    pure := @pure_Sum E;
    ap := @ap_Sum E
}.
Proof. all: monad. Defined.

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

Definition bind_Sum
  {E A B : Type} (sa : sum E A) (f : A -> sum E B) : sum E B :=
match sa with
    | inl e => inl e
    | inr a => f a
end.

Hint Unfold bind_Sum : HSLib.

Instance MonadSum (A : Type) : Monad (sum A) :=
{
    is_applicative := ApplicativeSum A;
    bind := @bind_Sum A
}.
Proof. all: monad. Defined.

Definition foldMap_Sum
  {E A : Type} {M : Monoid} (f : A -> M) (x : sum E A) : M :=
match x with
    | inl _ => neutr
    | inr a => f a
end.

Hint Unfold foldMap_Sum : HSLib.

Instance FoldableSum (E : Type) : Foldable (sum E) :=
{
    foldMap := @foldMap_Sum E
}.
Proof. monad. Defined.