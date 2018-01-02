Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Module Join.
Require Import HSLib.MonadJoin.Monad.
Include HSLib.MonadJoin.Monad.
End Join.

Module Bind.
Require Import HSLib.MonadBind.Monad.
Include HSLib.MonadBind.Monad.
End Bind.

Module Comp.
Require Import HSLib.MonadComp.Monad.
Include HSLib.MonadComp.Monad.
End Comp.

Instance JoinToBind (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_functor := @Join.is_functor M inst;
    ret := @Join.ret M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
        (fmap f .> Join.join) ma
}.
Proof.
(*  Focus 2. intros. Print Join.Monad. unfold compose.*)
  intros.
  unfold compose.
  Print Join.Monad.
  assert (H := Join.join_law).
  specialize (H A). unfold compose in H.
  Print Applicative.
  Print Functor.
  Search Join.join.
  Search Join.ret.
  cut (fmap f (Join.ret a) = Join.ret (f a)).
    intros ->.
    Focus 2.

Abort.

Instance BindToComp (M : Type -> Type) (inst : Bind.Monad M)
  : Comp.Monad M :=
{
    is_functor := @Bind.is_functor M inst;
    ret := @Bind.ret M inst;
    compM := fun (A B C : Type) (f : A -> M B) (g : B -> M C) =>
        fun a : A => Bind.bind (f a) g
}.
Proof.
  all: intros; extensionality x.
    rewrite Bind.assoc. reflexivity.
    apply Bind.id_left.
    apply Bind.id_right.
Defined.

Instance BindToJoin (M : Type -> Type) (inst : Bind.Monad M)
  : Join.Monad M :=
{
    is_functor := @Bind.is_functor M inst;
    ret := @Bind.ret M inst;
    join := fun (A : Type) (x : M (M A)) =>
        Bind.bind x id
}.
Proof.
  intros. unfold compose. extensionality x.
    rewrite Bind.assoc.
  Focus 2. intros. Print Bind.Monad. unfold compose.
    extensionality x. rewrite Bind.id_left.
Abort.