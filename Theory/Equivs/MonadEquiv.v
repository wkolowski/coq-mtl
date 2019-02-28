Require Import Control.

Require MonadJoin.
Require MonadBind.
Require MonadComp.

Module Join.
Include MonadJoin.
End Join.

Module Bind.
Include MonadBind.
End Bind.

Module Comp.
Include MonadComp.
End Comp.

(** * join-based definition *)

Instance Join_to_Monad
  (M : Type -> Type) (inst : Join.Monad M) : Monad M :=
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

Instance Monad_to_Join (M : Type -> Type) (inst : Monad M)
  : Join.Monad M :=
{
    is_applicative := @is_applicative M inst;
    join := @join M inst
}.
Proof.
  all: intros; unfold join, compose; try ext x.
    rewrite bind_assoc, bind_fmap. unfold compose, id. reflexivity.
    rewrite bind_pure_l. reflexivity.
    rewrite bind_fmap, <- bind_pure_r. f_equal.
    rewrite bind_fmap, fmap_bind. f_equal.
    rewrite !bind_ap. monad.
Defined.

(** * bind-based definition *)

Instance MonadBind_to_Monad
  (M : Type -> Type) (inst : Bind.Monad M) : Monad M :=
{
    is_applicative := @MonadBind.MonadBind_to_Applicative M inst;
    bind := @MonadBind.bind M inst;
}.
Proof. all: monad. Defined.

Instance Monad_to_MonadBind
  (M : Type -> Type) (inst : Monad M) : MonadBind.Monad M :=
{
    pure := @pure M inst;
    bind := @bind M inst;
}.
Proof. all: monad. Defined.

(** * compM-based definition *)

Instance Monad_to_MonadComp
  (M : Type -> Type) (inst : Monad M) : MonadComp.Monad M :=
{
    is_applicative := is_applicative;
    compM := @compM M inst;
}.
Proof. all: unfold compM; monad. Defined.