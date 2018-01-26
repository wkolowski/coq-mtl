Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition fmap_Cont {R A B : Type} (f : A -> B) (ca : Cont R A)
    : Cont R B := fun g : B -> R => ca (f .> g).

Instance FunctorCont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof. all: hs. Defined.

Definition ret_Cont
  {R A : Type} (a : A) : Cont R A :=
    fun f : A -> R => f a.

Definition ap_Cont
  {R A B : Type} (f : Cont R (A -> B)) (x : Cont R A) : Cont R B :=
    fun y : B -> R => f (fun h : A -> B => x (fun a : A => y (h a))).

Instance ApplicativeCont (R : Type) : Applicative (Cont R) :=
{
    is_functor := FunctorCont R;
    ret := @ret_Cont R;
    ap := @ap_Cont R
}.
Proof. all: hs. Defined.

Definition bind_Cont
  {R A B : Type} (ca : Cont R A) (f : A -> Cont R B) : Cont R B :=
    fun g : B -> R => ca (fun x : A => f x g).

Theorem Cont_not_Alternative :
  (forall R : Type, Alternative (Cont R)) -> False.
Proof.
  unfold Cont. intro. destruct (X False).
  apply aempty with False. trivial.
Qed.

Theorem Cont_not_CommutativeApplicative :
  ~ (forall R : Type, CommutativeApplicative _ (ApplicativeCont R)).
Proof.
  intro. destruct (H bool).
  specialize (ap_comm bool bool _ (fun _ => id) (const true) (const false)).
  compute in ap_comm. apply (f_equal (fun f => f id)) in ap_comm.
  inversion ap_comm.
Qed.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    bind := @bind_Cont R
}.
Proof. all: hs. Defined.

Hint Unfold Cont fmap_Cont ret_Cont ap_Cont bind_Cont : HSLib.

Require Import Arith.

(* TODO *) Definition callCC
  {R A B : Type} (f : (A -> Cont R B) -> Cont R A) : Cont R A :=
    fun ar : A -> R => f (fun (a : A) (_ : B -> R) => ar a) ar.