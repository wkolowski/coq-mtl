Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Instances.Cont.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.Monad.

Instance FunctorCont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof.
  intros. unfold fmap_Cont, id. trivial.
  intros. unfold fmap_Cont, id. trivial.
Defined.

Instance ApplicativeCont (R : Type) : Applicative (Cont R) :=
{
    is_functor := FunctorCont R;
    ret := @ret_Cont R;
    ap := @ap_Cont R
}.
Proof.
  trivial.
  trivial.
  trivial.
  trivial.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    ret := @ret_Cont R;
    join := @join_Cont R
}.
Proof.
  trivial.
  trivial.
Defined.