Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.MonadTrans.

Require Import HSLib.Instances.All.


Definition ContT (R : Type) (M : Type -> Type) (A : Type)
  : Type := (A -> M R) -> M R.

Definition fmap_ContT
  (R : Type) (M : Type -> Type) (inst : Functor M)
  (A B : Type) (f : A -> B) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => y (f a)).

Hint Unfold ContT fmap_ContT : HSLib.

Instance FunctorContT
  (R : Type) (M : Type -> Type) (inst : Functor M) : Functor (ContT R M) :=
{
    fmap := @fmap_ContT R M inst
}.
Proof. all: trivial. Defined.

Definition ret_ContT
  (R : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : ContT R M A := fun y : A -> M R => y x.

Definition ap_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : ContT R M (A -> B)) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => f (fun h : A -> B => x (fun a : A => y (h a))).

Hint Unfold ret_ContT ap_ContT : HSLib.

Instance Applicative_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) : Applicative (ContT R M) :=
{
    is_functor := FunctorContT R M inst;
    ret := @ret_ContT R M inst;
    ap := @ap_ContT R M inst
}.
Proof. all: reflexivity. Defined.

Theorem ContT_not_Alternative :
  (forall (R : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (ContT R M)) -> False.
Proof.
  intros. destruct (X False Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. apply aempty. trivial.
Qed.

Definition aempty_ContT
  (R : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : ContT R M A := fun _ => aempty.

Definition aplus_ContT
  (R : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (x y : ContT R M A) : ContT R M A :=
    fun c => x c <|> y c.

Hint Unfold aempty_ContT aplus_ContT : HSLib.

Instance Alternative_ContT
  (R : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  : Alternative (ContT R M) :=
{
    is_applicative := @Applicative_ContT R M instM;
    aempty := @aempty_ContT R M instM instA;
    aplus := @aplus_ContT R M instM instA;
}.
Proof. all: monad. Defined.

Definition bind_ContT
  (R : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : ContT R M A) (f : A -> ContT R M B) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => f a y).

Hint Unfold bind_ContT : HSLib.

Instance Monad_ContT (R : Type) (M : Type -> Type) {inst : Monad M}
    : Monad (ContT R M) :=
{
    is_applicative := Applicative_ContT R M inst;
    bind := @bind_ContT R M inst
}.
Proof. all: reflexivity. Defined.

Theorem ContT_not_MonadPlus :
  (forall (R : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (ContT R M)) -> False.
Proof.
  intros. apply ContT_not_Alternative.
  intros. destruct (X R M inst). assumption.
Qed.

Instance MonadPlus_ContT
  (R : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  : MonadPlus (ContT R M) :=
{
    is_monad := @Monad_ContT R M instM;
    is_alternative := @Alternative_ContT R M instM instA;
}.
Proof.
  all: reflexivity.
Defined.

Definition lift_ContT
  (R : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : ContT R M A :=
      fun y : A -> M R => @bind M inst _ _ ma (fun a : A => y a).

Hint Unfold lift_ContT : HSLib.

Instance MonadTrans_ContT (R : Type) : MonadTrans (ContT R) :=
{
    is_monad := @Monad_ContT R;
    lift := @lift_ContT R;
}.
Proof. all: monad. Defined.