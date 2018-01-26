Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.

Require Export HSLib.Misc.Monoid.

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

Definition ret_Writer
  {W : Monoid} {A : Type} (a : A) : Writer W A := (a, neutr).

Definition ap_Writer
  {W : Monoid} {A B : Type} (wf : Writer W (A -> B)) (wa : Writer W A)
    : Writer W B := let '((f, w), (a, w')) := (wf, wa) in (f a, op w w').

Hint Unfold ret_Writer ap_Writer : HSLib.

Instance ApplicativeWriter (W : Monoid) : Applicative (Writer W) :=
{
    is_functor := FunctorWriter W;
    ret := @ret_Writer W;
    ap := @ap_Writer W
}.
Proof. all: monad. Defined.

Instance Monoid_bool_andb : Monoid :=
{
    carr := bool;
    neutr := true;
    op := andb;
}.
Proof.
  all: intros; repeat
  match goal with
      | b : bool |- _ => destruct b
  end; cbn; reflexivity.
Defined.

Instance Monoid_list_app (A : Type) : Monoid :=
{
    carr := list A;
    neutr := [];
    op := @app A;
}.
Proof.
  all: intros.
    reflexivity.
    rewrite app_nil_r. reflexivity.
    rewrite app_assoc. reflexivity.
Defined.

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