Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition ContT (R : Type) (M : Type -> Type) (A : Type)
  : Type := (A -> M R) -> M R.

Definition fmap_ContT
  (R : Type) (M : Type -> Type) (inst : Functor M)
  (A B : Type) (f : A -> B) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => y (f a)).

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

Instance ApplicativeContT
  (R : Type) (M : Type -> Type) (inst : Monad M) : Applicative (ContT R M) :=
{
    is_functor := FunctorContT R M inst;
    ret := @ret_ContT R M inst;
    ap := @ap_ContT R M inst
}.
Proof. all: reflexivity. Defined.

Definition bind_ContT
  (R : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : ContT R M A) (f : A -> ContT R M B) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => f a y).

Instance Monad_ContT (R : Type) (M : Type -> Type) {inst : Monad M}
    : Monad (ContT R M) :=
{
    is_applicative := ApplicativeContT R M inst;
    bind := @bind_ContT R M inst
}.
Proof. all: reflexivity. Defined.

Definition lift_ContT
  (R : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : ContT R M A :=
      fun y : A -> M R => @bind M inst _ _ ma (fun a : A => y a).

Instance MonadTrans_ContT (R : Type) : MonadTrans (ContT R) :=
{
    is_monad := @Monad_ContT R;
    lift := @lift_ContT R;
}.
Proof.
  all: cbn; intros; unfold lift_ContT, ret_ContT, bind_ContT; monad.
Defined.