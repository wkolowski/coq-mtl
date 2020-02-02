Require Import Control.All.
Require Import Control.Monad.Class.MonadWriter.

Require Import Misc.Monoid.

(** [Writer W A] represents a computation that returns a result of type [A]
    and has access to a log of messages of type [W]. [W] is a monoid whose
    operation represents the concatenation of messages. *)
Definition Writer (W : Monoid) (A : Type) : Type := (A * W)%type.

(** We can map over [Writer W A] by applying the function to the result of
    the computation, without touching the log. *)
Definition fmap_Writer
  {W : Monoid} {A B : Type} (f : A -> B) (wa : Writer W A) : Writer W B :=
    let (a, w) := wa in (f a, w).

Hint Unfold fmap_Writer : CoqMTL.

#[refine]
Instance Functor_Writer (W : Monoid) : Functor (Writer W) :=
{
    fmap := @fmap_Writer W
}.
Proof. all: monad. Defined.

(** We can turn a value into a computation by placing it along an empty log,
    which is represented by the neutral element of the monoid [W]. *)
Definition pure_Writer
  {W : Monoid} {A : Type} (a : A) : Writer W A := (a, neutr).

(** We can apply a computation which returns a function to a computation
    which returns an argument by running them, applying the function to
    the argument and concatenating the produced logs (first the log of
    the function, then the log of the argument). *)
Definition ap_Writer
  {W : Monoid} {A B : Type} (wf : Writer W (A -> B)) (wa : Writer W A)
  : Writer W B :=
    let (f, w) := wf in
    let (a, w') := wa in (f a, op w w').

Hint Unfold pure_Writer ap_Writer : CoqMTL.

#[refine]
Instance Applicative_Writer (W : Monoid) : Applicative (Writer W) :=
{
    is_functor := Functor_Writer W;
    pure := @pure_Writer W;
    ap := @ap_Writer W
}.
Proof. all: monad. Defined.

(** In general, [Writer W] is a commutative applicative functor if the
    operation of concatenating logs is commutative. *)

Lemma Writer_not_CommutativeApplicative :
  ~ (forall W : Monoid, CommutativeApplicative _ (Applicative_Writer W)).
Proof.
  intro. destruct (H (Monoid_list_app bool)). unfold Writer in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (42, [true; false]) (43, [false; true])).
  compute in ap_comm. congruence.
Qed.

Instance CommutativeApplicative_Writer
  (W : Monoid) (H : forall x y : W, op x y = op y x)
  : CommutativeApplicative (Writer W) (Applicative_Writer W).
Proof.
  split. monad. unfold flip. f_equal. apply H.
Defined.

(** [Writer W] also doesn't always have [Alternative] structure, because
    it's argument may be an empty type. There's probably no simple way
    to fix this like in the case of [CommutativeApplicative]. *)
Lemma Writer_not_Alternative :
  forall W : Monoid, Alternative (Writer W) -> False.
Proof.
  destruct 1. destruct (aempty False). assumption.
Qed.

(** We can bind a computation to a function which returns a computation
    by first computing the argument and then running the computation
    returned by the function. In the meantime, we concatenate the logs. *)
Definition bind_Writer
  {W : Monoid} {A B : Type} (wa : Writer W A) (f : A -> Writer W B)
    : Writer W B :=
      let (a, w) := wa in
      let (b, w') := f a in (b, op w w').

Hint Unfold bind_Writer : CoqMTL.

#[refine]
Instance Monad_Writer (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := Applicative_Writer W;
    bind := @bind_Writer W
}.
Proof. all: monad. Defined.

(** Of course [Writer W] is the primordial example of [MonadWriter]. We
    can [tell] by just putting a message along [tt] and [listen] by
    moving the messages from the log to the result of the computation. *)
#[refine]
Instance MonadWriter_Writer (W : Monoid)
  : MonadWriter W (Writer W) (Monad_Writer W) :=
{
    tell := fun w => (tt, w);
    listen := fun A '(a, w) => ((a, w), neutr);
(*    pass := fun A '((a, f), w) => (a, f w);*)
}.
Proof.
  1-2: try reflexivity.
  intros A [a w]. cbn. reflexivity.
Defined.