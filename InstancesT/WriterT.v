Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Require Export HSLib.Monoid.

Open Scope type_scope.

Definition WriterT (W : Monoid) (M : Type -> Type) (A : Type)
  : Type := M (A * W).

Definition fmap_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> B)
  (x : WriterT W M A) : WriterT W M B :=
(*    @bind M inst _ _ x (fun '(a, w) => ret (f a, w)).*)
    fmap (fun '(a, w) => (f a, w)) x.

Instance Functor_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} : Functor (WriterT W M) :=
{
    fmap := @fmap_WriterT W M inst
}.
Proof.
  all: intros; unfold fmap_WriterT; ext x.
    match goal with
        | |- ?f ?g ?h = _ => replace (f g h) with (f id h)
    end.
      rewrite fmap_pres_id. reflexivity.
      f_equal. ext p. destruct p. reflexivity.
    unfold compose;
    match goal with
        | |- fmap ?f _ = fmap ?g (fmap ?h _) => replace f with (h .> g)
    end.
      rewrite fmap_pres_comp. unfold compose. reflexivity.
      ext p. destruct p. unfold compose. reflexivity.
Defined.

Definition ret_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : WriterT W M A := ret (x, neutr).

Definition ap_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mf : WriterT W M (A -> B)) (mx : WriterT W M A) : WriterT W M B :=
    @bind M inst _ _ mf (fun '(f, w) =>
    @bind M inst _ _ mx (fun '(x, w') =>
      ret (f x, op w w'))).

Instance Applicative_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M)
  : Applicative (WriterT W M) :=
{
    is_functor := @Functor_WriterT W M inst;
    ret := @ret_WriterT W M inst;
    ap := @ap_WriterT W M inst;
}.
Proof.
  all: cbn; unfold WriterT, fmap_WriterT, ret_WriterT, ap_WriterT; monad;
  rewrite ?id_left, ?id_right, ?op_assoc; try reflexivity.
Defined.

Hint Rewrite @id_left @id_right @op_assoc : monoid.

Ltac monoid := autorewrite with monoid; try congruence.

Definition bind_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : WriterT W M A) (f : A -> WriterT W M B) : WriterT W M B :=
    @bind M inst _ _ x (fun '(a, w) =>
    @bind M inst _ _ (f a) (fun '(b, w') =>
      ret (b, op w w'))).

Instance Monad_WriterT
  (W : Monoid) (M : Type -> Type) {inst : Monad M} : Monad (WriterT W M) :=
{
    is_applicative := @Applicative_WriterT W M inst;
    bind := @bind_WriterT W M inst;
}.
Proof.
  all: cbn;
  unfold WriterT, fmap_WriterT, ret_WriterT, ap_WriterT, bind_WriterT;
  monad; monoid.
Defined.

Definition lift_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : WriterT W M A := fmap (fun x : A => (x, neutr)) ma.

Instance MonadTrans_WriterT (W : Monoid) : MonadTrans (WriterT W) :=
{
    is_monad := @Monad_WriterT W;
    lift := @lift_WriterT W;
}.
Proof.
  all: cbn; intros; unfold WriterT, lift_WriterT, ret_WriterT, bind_WriterT.
  monad.
  monad. unfold compose. monad. unfold compose. monoid.
Defined.