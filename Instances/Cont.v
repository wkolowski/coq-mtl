Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition fmap_Cont {R A B : Type} (f : A -> B) (ca : Cont R A)
    : Cont R B := fun g : B -> R => ca (f .> g).

Instance FunctorCont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof. all: reflexivity. Defined.

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
Proof. all: reflexivity. Defined.

Definition join_Cont
  {R A : Type} (cca : Cont R (Cont R A)) : Cont R A :=
    fun f : A -> R => cca (fun g : (A -> R) -> R => g f).

Definition bind_Cont
  {R A B : Type} (ca : Cont R A) (f : A -> Cont R B) : Cont R B :=
    fun g : B -> R => ca (fun x : A => f x g).

Definition compM_Cont
  {R A B C : Type} (f : A -> Cont R B) (g : B -> Cont R C) (a : A)
    : Cont R C := fun y : C -> R => f a (fun b : B => g b y).

Theorem Cont_not_Alternative :
  (forall R : Type, Alternative (Cont R)) -> False.
Proof.
  unfold Cont. intro. destruct (X False).
  apply aempty with False. trivial.
Qed.