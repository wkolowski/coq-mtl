Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.MonadJoin.

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition fmap_Cont {R A B : Type} (f : A -> B) (ca : Cont R A)
    : Cont R B := fun g : B -> R => ca (f .> g).

Instance FunctorCont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof.
  intros. unfold fmap_Cont, id. trivial.
  intros. unfold fmap_Cont, id. trivial.
Defined.

Definition ret_Cont {R A : Type} (a : A) : Cont R A :=
    fun f : A -> R => f a.

Definition ap_Cont {R A B : Type} (cf : Cont R (A -> B)) (ca : Cont R A)
    : Cont R B := fun br : B -> R => ca (fun a : A => cf (fun ab : A -> B =>
        br (ab a))).
(*
. unfold Cont in *. intro. apply ca. intro. apply cf. intro. apply X. apply X1. apply X0.
Defined.
Print ap_Cont.
 := fun rb : B -> R => *)

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

Definition join_Cont {R A : Type} (cca : Cont R (Cont R A)) : Cont R A :=
    fun f : A -> R => cca (fun g : (A -> R) -> R => g f).

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    ret := @ret_Cont R;
    join := @join_Cont R
}.
Proof.
  trivial.
  trivial.
Defined.