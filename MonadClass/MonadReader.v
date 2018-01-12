Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.MonadBind.Monad.

Class MonadReader
  (R : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    ask : M R;
    local : (R -> R) -> M R -> M R;
}.

Section MonadState_funs.

Variables
  (R : Type)
  (M : Type -> Type)
  (inst : Monad M)
  (inst' : MonadReader R M inst).

(** Ask for a function of the environment. *)
Definition asks {A : Type} (f : R -> A) : M A :=
  do
    r <- ask;
    ret $ f r.