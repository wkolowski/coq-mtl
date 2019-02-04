Require Import HSLib.Base.
Require Import Control.Monad.
Require Import Control.Monad.Trans.

Class MonadReader
  (R : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    ask : M R;
(*    local : (R -> R) -> M R -> M R;*)
    ask_ask : ask >> ask = ask;
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

Instance MonadReader_MonadTrans
  (T : (Type -> Type) -> Type -> Type) (instT : MonadTrans T)
  (M : Type -> Type) (instM : Monad M)
  (R : Type) (instMR : MonadReader R M instM)
  : MonadReader R (T M) (is_monad _ instM) :=
{
    ask := lift ask
}.
Proof.
  rewrite lift_constrA, ask_ask. reflexivity.
Defined.