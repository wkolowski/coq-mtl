Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Instances.Reader.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.Monad.

Instance FunctorReader (R : Type) : Functor (Reader R) :=
{
    fmap := @fmap_Reader R
}.
Proof.
  intros. extensionality ra. extensionality r. unfold fmap_Reader, id. trivial.
  intros. extensionality ra. extensionality r. unfold fmap_Reader, id, compose.
    trivial.
Defined.

Instance ApplicativeReader (R : Type) : Applicative (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    ap := @ap_Reader R
}.
Proof.
  trivial.
  trivial.
  trivial.
  trivial.
Defined.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    ret := @ret_Reader R;
    join := @join_Reader R
}.
Proof.
  trivial.
  trivial.
Defined.