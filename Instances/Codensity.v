Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Codensity (A : Type) : Type :=
  forall {R : Type}, (A -> R) -> R.

Definition fmap_Codensity
  {A B : Type} (f : A -> B) (x : Codensity A) : Codensity B :=
    fun (R : Type) (y : B -> R) => x R (fun a : A => y (f a)).

Instance FunctorCodensity : Functor Codensity :=
{
    fmap := @fmap_Codensity
}.
Proof. all: reflexivity. Defined.

Definition ret_Codensity
  {A : Type} (a : A) : Codensity A :=
    fun (R : Type) (f : A -> R) => f a.

Definition ap_Codensity
  {A B : Type} (f : Codensity (A -> B)) (x : Codensity A) : Codensity B :=
    fun (R : Type) (y : B -> R) =>
      f R (fun h : A -> B => x R (fun a : A => y (h a))).

Instance ApplicativeCodensity : Applicative Codensity :=
{
    is_functor := FunctorCodensity;
    ret := @ret_Codensity;
    ap := @ap_Codensity;
}.
Proof. all: reflexivity. Defined.

Definition bind_Codensity
  {A B : Type} (ca : Codensity A) (f : A -> Codensity B) : Codensity B :=
    fun (R : Type) (g : B -> R) => ca R (fun x : A => f x R g).

Theorem Codensity_not_Alternative :
  Alternative Codensity -> False.
Proof.
  destruct 1. unfold Codensity in *.
  apply (aempty False). intro. assumption.
Qed.

Require Import HSLib.MonadBind.Monad.

Instance MonadCodensity : Monad Codensity :=
{
    is_applicative := @ApplicativeCodensity;
    bind := @bind_Codensity;
}.
Proof. all: reflexivity. Defined.

Definition callCC_Type : Type :=
  forall A B : Type, ((A -> Codensity B) -> Codensity A) -> Codensity A.

(* TODO: why no callCC? *)
Theorem no_callCC :
  callCC_Type -> False.
Proof.
  unfold callCC_Type, Codensity. intro.
  apply (X False unit).
Abort.