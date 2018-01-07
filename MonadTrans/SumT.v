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

Hint Rewrite @bind_ret_l @bind_ret_r @assoc @fmap_ret @bind_fmap @fmap_bind
  : monad.

Instance Applicative_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (SumT E M) :=
{
    is_functor := @Functor_SumT M inst E;
    ret := @ret_SumT M inst E;
    ap := @ap_SumT M inst E;
}.
Proof.
  Ltac wut := repeat (
  match goal with
      | |- ?x >>= _ = ?x >>= _ => f_equal
      | |- context [_ >>= ?f] =>
          match f with
              | (fun _ : ?A => _) =>
                  match type of f with
                      | ?T -> _ => replace f with (@ret _ _ A)
                  end
          end
      | |- context [match ?x with _ => _ end] => destruct x
      | |- ret = fun _ => _ => let x := fresh "x" in ext x
      | |- (fun _ => _) = (fun _ => _) => let x := fresh "x" in ext x
      | |- context [id] => unfold id
      | |- context [_ .> _] => unfold compose
      | _ => autorewrite with monad
  end; try congruence).
  1-5: unfold SumT, ret_SumT, ap_SumT; intros.
    wut. wut. wut. wut. wut.
Abort.

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