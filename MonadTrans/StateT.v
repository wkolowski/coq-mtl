Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Open Scope type_scope.

Definition StateT (S : Type) (M : Type -> Type) (A : Type)
  : Type := S -> M (A * S).

Definition fmap_StateT
  {M : Type -> Type} {inst : Monad M} {S A B : Type} (f : A -> B)
  : StateT S M A -> StateT S M B :=
    fun (x : StateT S M A) (s : S) =>
      x s >>= fun '(a, s') => ret (f a, s').
(*
    fmap (fun '(a, s) => (f a, s)) (x s).
*)

Instance Functor_StateT
  {M : Type -> Type} {inst : Monad M} {S : Type} : Functor (StateT S M) :=
{
    fmap := @fmap_StateT M inst S
}.
Proof.
  all: intros; unfold fmap_StateT; ext x; ext s.
    replace (x s >>= _ = _) with (x s >>= ret = id x s).
      rewrite bind_ret_r. reflexivity.
      do 2 f_equal. ext p. destruct p. reflexivity.
    unfold compose. rewrite assoc. f_equal. ext p. destruct p.
      rewrite bind_ret_l. reflexivity.
Defined.

Definition ret_StateT
  {M : Type -> Type} {inst : Monad M} {S A : Type} (x : A)
    : StateT S M A := fun s => ret (x, s).

Definition bind_StateT
  {M : Type -> Type} {inst : Monad M} {S A B : Type}
  (x : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
    fun s : S => x s >>= (fun '(a, s') => f a s').

Instance Monad_StateT
  (S : Type) (M : Type -> Type) {inst : Monad M} : Monad (StateT S M) :=
{
    is_functor := @Functor_StateT M inst S;
    ret := @ret_StateT M inst S;
    bind := @bind_StateT M inst S;
}.
Proof.
  all: cbn; intros; unfold fmap_StateT, ret_StateT, bind_StateT; ext s.
    rewrite bind_ret_l. reflexivity.
    replace (ma s >>= _) with (ma s >>= ret).
      rewrite bind_ret_r. reflexivity.
      f_equal. ext p. destruct p. reflexivity.
    rewrite assoc. f_equal. ext p. destruct p. reflexivity.
    rewrite bind_ret_l. reflexivity.
    rewrite assoc. f_equal. ext p. destruct p. rewrite bind_ret_l.
      unfold compose. reflexivity.
    rewrite assoc. f_equal. ext p. destruct p. reflexivity.
Defined.

Definition lift_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : StateT S M A := fun s : S => ma >>= fun a : A => ret (a, s).

Instance MonadTrans_StateT (S : Type) : MonadTrans (StateT S) :=
{
    is_monad := @Monad_StateT S;
    lift := @lift_StateT S;
}.
Proof.
  all: cbn; intros; unfold lift_StateT, ret_StateT, bind_StateT; ext s.
    rewrite bind_ret_l. reflexivity.
    rewrite !assoc. f_equal. ext a. rewrite bind_ret_l. unfold compose.
      reflexivity.
Defined.