Require Import Control.
Require Import Misc.Monoid.

Definition Writer (W : Monoid) (A : Type) : Type := (A * W)%type.

Definition fmap_Writer
  {W : Monoid} {A B : Type} (f : A -> B) (wa : Writer W A) : Writer W B :=
match wa with
    | (a, w) => (f a, w)
end.

Hint Unfold Writer fmap_Writer : HSLib.

Instance FunctorWriter (W : Monoid) : Functor (Writer W) :=
{
    fmap := @fmap_Writer W
}.
Proof. all: monad. Defined.

Definition pure_Writer
  {W : Monoid} {A : Type} (a : A) : Writer W A := (a, neutr).

Definition ap_Writer
  {W : Monoid} {A B : Type} (wf : Writer W (A -> B)) (wa : Writer W A)
    : Writer W B := let '((f, w), (a, w')) := (wf, wa) in (f a, op w w').

Hint Unfold pure_Writer ap_Writer : HSLib.

Instance ApplicativeWriter (W : Monoid) : Applicative (Writer W) :=
{
    is_functor := FunctorWriter W;
    pure := @pure_Writer W;
    ap := @ap_Writer W
}.
Proof. all: monad. Defined.

Theorem Writer_not_CommutativeApplicative :
  ~ (forall W : Monoid, CommutativeApplicative _ (ApplicativeWriter W)).
Proof.
  intro. destruct (H (Monoid_list_app bool)). unfold Writer in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (42, [true; false]) (43, [false; true])).
  compute in ap_comm. congruence.
Qed.

Theorem Writer_not_Alternative :
  forall W : Monoid, Alternative (Writer W) -> False.
Proof.
  destruct 1. destruct (aempty False). assumption.
Qed.

Definition bind_Writer
  {W : Monoid} {A B : Type} (wa : Writer W A) (f : A -> Writer W B)
    : Writer W B :=
      let (a, w) := wa in
      let (b, w') := f a in (b, op w w').

Hint Unfold bind_Writer : HSLib.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := ApplicativeWriter W;
    bind := @bind_Writer W
}.
Proof. all: monad. Defined.