Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.MonadTrans.

Require Import HSLib.Instances.All.
Require Import Control.MonadInst.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Definition fmap_Option {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Definition fmap_OptionT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : OptionT M A -> OptionT M B :=
    fmap (fmap_Option f).

Instance Functor_OptionT (M : Type -> Type) {inst : Functor M}
    : Functor (OptionT M) :=
{
    fmap := fmap_OptionT
}.
Proof.
  all: unfold fmap_OptionT, fmap_Option; mtrans.
Defined.

Definition ret_OptionT
  {M : Type -> Type} {inst : Monad M} {A : Type} (x : A) : OptionT M A :=
    ret $ Some x.

Definition ap_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mof : OptionT M (A -> B)) (moa : OptionT M A) : OptionT M B :=
    @bind M inst _ _ mof (fun of =>
    match of with
        | Some f =>
            @bind M inst _ _ moa (fun oa =>
            match oa with
                | Some a => ret (Some (f a))
                | None => ret None
            end)
        | _ => ret None
    end).

Instance Applicative_OptionT
  (M : Type -> Type) (inst : Monad M) : Applicative (OptionT M) :=
{
    is_functor := @Functor_OptionT M inst;
    ret := @ret_OptionT M inst;
    ap := @ap_OptionT M inst;
}.
Proof.
  all: cbn; unfold OptionT, fmap_OptionT, ret_OptionT, ap_OptionT; monad.
Defined.

Definition aempty_OptionT
  (M : Type -> Type) (inst : Monad M) (A : Type) : OptionT M A :=
    ret None.

Definition aplus_OptionT
  (M : Type -> Type) (inst : Monad M) (A : Type) (mox moy : OptionT M A)
    : OptionT M A :=
    @bind M inst _ _ mox (fun ox =>
    @bind M inst _ _ moy (fun oy =>
    match ox, oy with
        | Some x, _ => ret (Some x)
        | _, Some y => ret (Some y)
        | _, _ => ret None
    end)).

Instance Alternative_OptionT
  (M : Type -> Type) (inst : Monad M) : Alternative (OptionT M) :=
{
    is_applicative := Applicative_OptionT M inst;
    aempty := aempty_OptionT M inst;
    aplus := aplus_OptionT M inst;
}.
Proof.
  all: unfold OptionT, aplus_OptionT, aempty_OptionT; monad.
Defined.

Definition bind_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (moa : OptionT M A) (f : A -> OptionT M B) : OptionT M B :=
    @bind M inst (option A) (option B) moa (fun oa : option A =>
    match oa with
        | None => ret None
        | Some a => f a
    end).

Instance Monad_OptionT
  (M : Type -> Type) (inst : Monad M) : Monad (OptionT M) :=
{
    is_applicative := Applicative_OptionT M inst;
    bind := @bind_OptionT M inst
}.
Proof.
  all: cbn;
  unfold OptionT, fmap_OptionT, ret_OptionT, ap_OptionT, bind_OptionT; monad.
Defined.

Instance MonadPlus_OptionT
  (M : Type -> Type) (inst : Monad M) : MonadPlus (OptionT M) :=
{
    is_monad := Monad_OptionT M inst;
    is_alternative := Alternative_OptionT M inst;
}.

Definition lift_OptionT {M : Type -> Type} {_inst : Monad M} {A : Type}
  (ma : M A) : OptionT M A := fmap Some ma.

Instance MonadTrans_OptionT : MonadTrans OptionT :=
{
    is_monad := @Monad_OptionT;
    lift := @lift_OptionT;
}.
Proof.
  all: cbn; unfold lift_OptionT, ret_OptionT, bind_OptionT, compose; monad.
Defined.