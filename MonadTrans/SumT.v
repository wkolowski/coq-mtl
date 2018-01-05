Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

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
    is_functor := @Functor_SumT M inst E;
    ret := @ret_SumT M inst E;
    bind := @bind_SumT M inst E;
}.
Proof.
  all: cbn; intros; unfold fmap_SumT, ret_SumT, bind_SumT.
    rewrite bind_ret_l. reflexivity.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (E + A))
    end.
      rewrite bind_ret_r. reflexivity.
      ext oa. destruct oa; reflexivity.
    rewrite assoc. f_equal. ext sa. destruct sa.
      rewrite bind_ret_l. reflexivity.
      reflexivity.
    rewrite fmap_ret. reflexivity.
    rewrite bind_fmap. unfold compose. f_equal. ext oa.
      destruct oa; cbn; reflexivity.
    rewrite fmap_bind. f_equal. ext sa. destruct sa; cbn.
      rewrite fmap_ret. reflexivity.
      reflexivity.
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
  all: cbn; intros; unfold lift_SumT, ret_SumT, bind_SumT.
    rewrite fmap_ret. reflexivity.
    rewrite bind_fmap. unfold compose. rewrite fmap_bind. reflexivity.
Defined.