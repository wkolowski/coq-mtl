Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.

Module Join.
Require Import HSLib.MonadJoin.Monad.
Include HSLib.MonadJoin.Monad.
End Join.

Module Bind.
Require Import Control.Monad.
Include Control.Monad.
End Bind.

Require Import Control.Applicative.
Require Import HSLib.Misc.KleisliTriple.

Instance JoinToBind
  (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_applicative := @Join.is_applicative M inst;
    bind := @Join.bind M inst
}.
Proof.
  apply Join.bind_pure_l.
  apply Join.bind_pure_r.
  apply Join.assoc.
  apply Join.bind_ap.
Defined.

Instance BindToJoin (M : Type -> Type) (inst : Bind.Monad M)
  : Join.Monad M :=
{
    is_applicative := @Bind.is_applicative M inst;
    join := @Bind.join M inst
}.
Proof.
  all: intros; unfold Bind.join, compose; try ext x.
    rewrite Bind.bind_assoc, Bind.bind_fmap. unfold compose, id. reflexivity.
    rewrite Bind.bind_pure_l. reflexivity.
    rewrite Bind.bind_fmap, <- Bind.bind_pure_r. f_equal.
    rewrite Bind.bind_fmap, Bind.fmap_bind. f_equal.
    rewrite !Bind.bind_ap. Bind.monad.
Defined.