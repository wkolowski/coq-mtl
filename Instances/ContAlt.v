Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Cont (A : Type) : Type :=
  forall {R : Type}, (A -> R) -> R.

Definition fmap_Cont
  {A B : Type} (f : A -> B) (x : Cont A) : Cont B :=
    fun (R : Type) (y : B -> R) => x R (fun a : A => y (f a)).

Instance FunctorCont : Functor Cont :=
{
    fmap := @fmap_Cont
}.
Proof. all: reflexivity. Defined.

Definition ret_Cont
  {A : Type} (a : A) : Cont A :=
    fun (R : Type) (f : A -> R) => f a.

Definition ap_Cont
  {A B : Type} (f : Cont (A -> B)) (x : Cont A) : Cont B :=
    fun (R : Type) (y : B -> R) =>
      f R (fun h : A -> B => x R (fun a : A => y (h a))).

Instance ApplicativeCont : Applicative Cont :=
{
    is_functor := FunctorCont;
    ret := @ret_Cont;
    ap := @ap_Cont;
}.
Proof. all: reflexivity. Defined.

(*Definition join_Cont
  {A : Type} (cca : Cont R (Cont R A)) : Cont R A :=
    fun f : A -> R => cca (fun g : (A -> R) -> R => g f).*)

Definition bind_Cont
  {A B : Type} (ca : Cont A) (f : A -> Cont B) : Cont B :=
    fun (R : Type) (g : B -> R) => ca R (fun x : A => f x R g).

(*Definition compM_Cont
  {A B C : Type} (f : A -> Cont R B) (g : B -> Cont R C) (a : A)
    : Cont R C := fun y : C -> R => f a (fun b : B => g b y).
*)
Theorem Cont_not_Alternative :
  Alternative Cont -> False.
Proof.
  destruct 1. unfold Cont in *.
  apply (aempty False). intro. assumption.
Qed.

Require Import HSLib.MonadBind.Monad.

Instance MonadCont : Monad Cont :=
{
    is_applicative := @ApplicativeCont;
    bind := @bind_Cont;
}.
Proof. all: reflexivity. Defined.

Definition addCPS (n m : nat) : Cont nat := ret (n + m).

Definition squareCPS (n : nat) : Cont nat := ret (n * n).

Definition pythagCPS (n m : nat) : Cont nat :=
  do
    nn <- squareCPS n;
    mm <- squareCPS m;
    addCPS nn mm.

Compute pythagCPS 2 3 _ id.

Definition callCC
  {A : Type} (f : (A -> forall B : Type, Cont B) -> Cont A) : Cont A.
Proof.
  unfold Cont in *. intros R y. apply f.
    Focus 2. trivial.
    intros a B Q z. apply z. apply f.
Abort.