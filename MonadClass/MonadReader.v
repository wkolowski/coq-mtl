Require Import HSLib.Base.
Require Import Control.Monad.

Class MonadReader
  (R : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    ask : M R;
    local : (R -> R) -> M R -> M R;
}.

Section MonadReader_funs.

Variables
  (R : Type)
  (M : Type -> Type)
  (inst : Monad M)
  (inst' : MonadReader R M inst).

(** Ask for a function of the environment. *)
Definition asks {A : Type} (f : R -> A) : M A :=
  do
    r <- ask;
    pure $ f r.

End MonadReader_funs.