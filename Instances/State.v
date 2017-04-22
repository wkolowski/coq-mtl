Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition State (S A : Type) := S -> A * S.

Definition fmap_State (S A B : Type) (f : A -> B) (st : State S A)
    : State S B := fun s : S => let (a, s') := st s in (f a, s').

Definition ret_State (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

Definition ap_State (S A B : Type) (sf : State S (A -> B)) (sa : State S A)
    : State S B := fun st : S =>
        let (f, stf) := sf st in
        let (a, sta) := sa stf in (f a, sta).

Definition join_State {S A : Type} (ssa : State S (State S A)) : State S A :=
    fun s : S => let (f, s') := ssa s in f s'.

Instance FunctorState (S : Type) : Functor (State S) :=
{
    fmap := @fmap_State S
}.
Proof.
  intros. unfold fmap_State, id. extensionality st. extensionality s.
    destruct (st s). reflexivity.
  intros. unfold fmap_State, compose, id. extensionality st. extensionality s.
    destruct (st s). reflexivity.
Defined.

Instance ApplicativeState (S : Type) : Applicative (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    ap := @ap_State S
}.
Proof.
  intros. unfold ret_State, ap_State. extensionality st.
    destruct (ax st). trivial.
  intros. unfold ret_State, ap_State. unfold State in *. extensionality st.
    destruct (ag st). destruct (af s). destruct (ax s0). trivial.
  intros. unfold ret_State, ap_State. extensionality st. trivial.
  intros. unfold ret_State, ap_State. extensionality st. destruct (f st).
    trivial.
Defined.

Theorem State_not_alternative : exists S : Type,
    Alternative (State S) -> False.
Proof.
  exists unit. destruct 1. destruct (aempty False).
    exact tt.
    assumption.
Qed.