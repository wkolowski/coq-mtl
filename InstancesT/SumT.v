Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

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
    @bind M inst _ _ msx (fun sx =>
      match sf, sx with
          | inr f, inr x => ret (inr (f x))
          | inl e, _ => ret (inl e)
          | _, inl e => ret (inl e)
      end)).

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
  Axiom huj : False. destruct huj. (* TODO *)
Defined.

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