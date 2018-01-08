Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition ReaderT (E : Type) (M : Type -> Type) (A : Type)
  : Type := E -> M A.

Definition fmap_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  : ReaderT E M A -> ReaderT E M B :=
    fun (x : ReaderT E M A) (e : E) => fmap f (x e).

Instance Functor_ReaderT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (ReaderT E M) :=
{
    fmap := @fmap_ReaderT M inst E
}.
Proof.
  all: intros; unfold fmap_ReaderT; ext x; ext e.
    rewrite fmap_pres_id. reflexivity.
    rewrite fmap_pres_comp. unfold compose. reflexivity.
Defined.

Definition ret_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A)
  : ReaderT E M A := fun _ => ret x.

Definition ap_ReaderT
  {E : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : ReaderT E M (A -> B)) (x : ReaderT E M A) : ReaderT E M B :=
    fun e : E => f e <*> x e.

Instance Applicative_ReaderT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (ReaderT E M) :=
{
    is_functor := @Functor_ReaderT M inst E;
    ret := @ret_ReaderT M inst E;
    ap := @ap_ReaderT E M inst;
}.
Proof.
  all: cbn; unfold fmap_ReaderT, ret_ReaderT, ap_ReaderT; intros; ext e;
  applicative.
Defined.

Definition bind_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (x : ReaderT E M A) (f : A -> ReaderT E M B) : ReaderT E M B :=
    fun e : E => x e >>= (fun a : A => f a e).

Instance Monad_ReaderT
  (E : Type) (M : Type -> Type) {inst : Monad M} : Monad (ReaderT E M) :=
{
    is_applicative := @Applicative_ReaderT E M inst;
    bind := @bind_ReaderT M inst E;
}.
Proof.
  all: cbn;
  unfold fmap_ReaderT, ret_ReaderT, ap_ReaderT, bind_ReaderT;
  monad.
Defined.

Definition lift_ReaderT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : ReaderT E M A := fun _ => ma.

Instance MonadTrans_ReaderT (E : Type) : MonadTrans (ReaderT E) :=
{
    is_monad := @Monad_ReaderT E;
    lift := @lift_ReaderT E;
}.
Proof. all: reflexivity. Defined.