Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Definition fmap_OptionT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : OptionT M A -> OptionT M B :=
    fmap (fun oa : option A =>
    match oa with
        | None => None
        | Some x => Some (f x)
    end).

Instance FunctorOptionT (M : Type -> Type) {inst : Functor M}
    : Functor (OptionT M) :=
{
    fmap := fmap_OptionT
}.
Proof.
  all: unfold fmap_OptionT; functor.
Defined.

Definition bind_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (moa : OptionT M A) (f : A -> OptionT M B) : OptionT M B :=
    @bind M inst (option A) (option B) moa (fun oa : option A =>
match oa with
    | None => ret None
    | Some a => f a
end).

Instance Monad_OptionT (M : Type -> Type) {inst : Monad M}
    : Monad (OptionT M) :=
{
    is_functor := FunctorOptionT M;
    ret := fun (A : Type) (x : A) => ret (Some x);
    bind := @bind_OptionT M inst
}.
Proof.
  all: cbn; intros; unfold fmap_OptionT, bind_OptionT.
    rewrite bind_ret_l. reflexivity.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (option A))
    end.
      rewrite bind_ret_r. reflexivity.
      ext oa. destruct oa; reflexivity.
    rewrite assoc. f_equal. ext oa. destruct oa.
      reflexivity.
      rewrite bind_ret_l. reflexivity.
    rewrite fmap_ret. reflexivity.
    rewrite bind_fmap. unfold compose. f_equal. ext oa.
      destruct oa; cbn; reflexivity.
    rewrite fmap_bind. f_equal. ext oa. destruct oa; cbn.
      reflexivity.
      rewrite fmap_ret. cbn. reflexivity.
Defined.
(*Restart.
  From mathcomp Require Import ssreflect.
  all: intros; unfold bind_OptionT; cbn.
    by rewrite bind_ret_l.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (option A))
    end.
      by rewrite bind_ret_r.
      by ext oa; case: oa.
    rewrite assoc. f_equal. by ext oa; case: oa; rewrite ?bind_ret_l.
    by rewrite fmap_ret.
    rewrite bind_fmap /compose. f_equal. by ext oa; case: oa.
    rewrite fmap_bind. f_equal. by ext oa; case oa; rewrite ?fmap_ret.
Defined.*)

Definition lift_OptionT {M : Type -> Type} {_inst : Monad M} {A : Type}
  (ma : M A) : OptionT M A := fmap Some ma.

Instance MonadTrans_OptionT : MonadTrans OptionT :=
{
    is_monad := @Monad_OptionT;
    lift := @lift_OptionT;
}.
Proof.
  all: intros; unfold lift_OptionT; cbn.
    rewrite fmap_ret. reflexivity.
    unfold bind_OptionT. rewrite bind_fmap. unfold compose.
      rewrite fmap_bind. reflexivity.
Defined.

(*Eval compute in @lift OptionT MonadTrans_OptionT list MonadList nat [5].*)