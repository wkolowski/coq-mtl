Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Monad.
Require Import Control.MonadTrans.

Definition ContT (R : Type) (M : Type -> Type) (A : Type)
  : Type := (A -> M R) -> M R.

Section ContT_instances.

Variables
  (R : Type)
  (M : Type -> Type)
  (inst : Monad M).

Definition fmap_ContT
  (A B : Type) (f : A -> B) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => y (f a)).

Instance FunctorContT : Functor (ContT R M) :=
{
    fmap := fmap_ContT
}.
Proof. all: reflexivity. Defined.

Definition ret_ContT (A : Type) (x : A) : ContT R M A :=
  fun y : A -> M R => y x.

Definition ap_ContT
  (A B : Type) (mf : ContT R M (A -> B)) (ma : ContT R M A) : ContT R M B :=
    fun y : B -> M R => mf (fun f : A -> B => ma (fun a : A => y (f a))).

Instance ApplicativeContT : Applicative (ContT R M) :=
{
    is_functor := FunctorContT;
    ret := ret_ContT;
    ap := ap_ContT;
}.
Proof. all: reflexivity. Defined.

Definition bind_ContT
  (A B : Type) (x : ContT R M A) (f : A -> ContT R M B) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => f a y).

Instance Monad_ContT : Monad (ContT R M) :=
{
    is_applicative := ApplicativeContT;
    bind := bind_ContT;
}.
Proof. all: reflexivity. Defined.

Definition lift_ContT
  (A : Type) (ma : M A) : ContT R M A :=
    fun y : A -> M R => @bind M inst _ _ ma (fun a : A => y a).

End ContT_instances.

Instance MonadTrans_ContT (R : Type) : MonadTrans (ContT R) :=
{
    is_monad := fun M _ => @Monad_ContT R M;
    lift := @lift_ContT R;
}.
Proof.
  all: cbn; intros; unfold lift_ContT, ret_ContT, bind_ContT; ext y.
    apply bind_ret_l.
    apply assoc.
Defined.