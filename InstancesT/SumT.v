Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.
Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadPlus.MonadPlus.
Require Import HSLib.MonadTrans.MonadTrans.

Require Import HSLib.Instances.All.
Require Import HSLib.MonadBind.MonadInst.

Definition SumT (E : Type) (M : Type -> Type) (A : Type)
  : Type := M (sum E A).

Definition fmap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  : SumT E M A -> SumT E M B :=
    fmap (fun sa : sum E A =>
    match sa with
        | inl e => inl e
        | inr a => inr (f a)
    end).

Instance Functor_SumT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (SumT E M) :=
{
    fmap := @fmap_SumT M inst E
}.
Proof.
  all: unfold fmap_SumT; functor.
Defined.

Definition ret_SumT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A)
  : SumT E M A := ret (inr x).

Definition ap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (msf : SumT E M (A -> B)) (msx : SumT E M A) : SumT E M B :=
    @bind M inst _ _ msf (fun sf =>
      match sf with
          | inl e => ret (inl e)
          | inr f =>
              @bind M inst _ _ msx (fun sx =>
              match sx with
                  | inl e => ret (inl e)
                  | inr x => ret (inr (f x))
              end)
      end).

Instance Applicative_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (SumT E M) :=
{
    is_functor := @Functor_SumT M inst E;
    ret := @ret_SumT M inst E;
    ap := @ap_SumT M inst E;
}.
Proof.
  1-5: cbn; unfold SumT, fmap_SumT, ret_SumT, ap_SumT; monad.
Defined.

Theorem SumT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (SumT E M)) -> False.
Proof.
  intros. destruct (X False Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. destruct aempty; assumption.
Qed.

Definition bind_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (ma : SumT E M A) (f : A -> SumT E M B) : SumT E M B :=
    @bind M inst _ _ ma (fun sa : E + A =>
    match sa with
        | inl e => ret (inl e)
        | inr a => f a
    end).

Instance Monad_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} : Monad (SumT E M) :=
{
    is_applicative := @Applicative_SumT E M inst;
    bind := @bind_SumT M inst E;
}.
Proof.
  all: cbn; unfold SumT, fmap_SumT, ret_SumT, ap_SumT, bind_SumT; monad.
Defined.

Theorem SumT_not_MonadPlus :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (SumT E M)) -> False.
Proof.
  intros. apply SumT_not_Alternative.
  intros. destruct (X E M inst). assumption.
Qed.

Definition lift_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
  : SumT E M A := fmap inr ma.

Instance MonadTrans_SumT (E : Type) : MonadTrans (SumT E) :=
{
    is_monad := @Monad_SumT E;
    lift := @lift_SumT E;
}.
Proof.
  all: cbn; intros; unfold lift_SumT, ret_SumT, bind_SumT; monad.
Defined.