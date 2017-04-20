Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Instances.State.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.Monad.

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

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    join := @join_State S
}.
Proof.
  intros. extensionality s3x. extensionality s1.
    simpl. unfold join_State, fmap_State, compose. destruct (s3x s1).
    destruct (s s0). trivial.
  intros. extensionality sx. extensionality s.
    simpl. unfold ret_State, join_State, fmap_State, compose.
    destruct (sx s). trivial.
Defined.