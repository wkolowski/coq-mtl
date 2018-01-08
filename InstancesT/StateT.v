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
      monad.
      do 2 f_equal. ext p. destruct p. reflexivity.
    unfold compose. rewrite assoc. f_equal. ext p. destruct p.
      monad.
Defined.

Definition ret_StateT
  {M : Type -> Type} {inst : Monad M} {S A : Type} (x : A)
    : StateT S M A := fun s => ret (x, s).

Definition ap_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (sf : StateT S M (A -> B)) (sa : StateT S M A) : StateT S M B :=
    fun st : S =>
      sf st >>= fun '(f, stf) =>
      sa stf >>= fun '(a, sta) =>
        ret (f a, sta).

Instance Applicative_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) : Applicative (StateT S M) :=
{
    is_functor := @Functor_StateT M inst S;
    ret := @ret_StateT M inst S;
    ap := @ap_StateT S M inst;
}.
Proof.
  all: cbn; unfold fmap_StateT, ret_StateT, ap_StateT; monad.
Defined.

Definition bind_StateT
  {M : Type -> Type} {inst : Monad M} {S A B : Type}
  (x : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
    fun s : S => x s >>= (fun '(a, s') => f a s').

Ltac st :=
  cbn; intros; 
repeat (monad; repeat match goal with
    | |- ?x >>= _ = ?x => rewrite <- bind_ret_r
    | |- ?x >>= _ = ?x >>= _ => f_equal
    | |- (fun _ => _) = _ => let x := fresh "x" in ext x
    | |- _ = (fun _ => _) => let x := fresh "x" in ext x
    | H : _ * _ |- _ => destruct H
end; monad).

Instance Monad_StateT
  (S : Type) (M : Type -> Type) {inst : Monad M} : Monad (StateT S M) :=
{
    is_applicative := @Applicative_StateT S M inst;
    bind := @bind_StateT M inst S;
}.
Proof.
  all: cbn; unfold fmap_StateT, ret_StateT, ap_StateT, bind_StateT; monad.
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
  all: cbn; unfold ret_StateT, bind_StateT, lift_StateT; monad.
Defined.