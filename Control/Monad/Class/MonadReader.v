From CoqMTL Require Export Control.Monad.
From CoqMTL Require Import Control.Monad.Trans.

(** Reader monad that provides access to some kind of environment.
    We can ask for the contents of the environment and if we ask
    twice in a row then it's as if we had asked only once. *)
Class MonadReader
  (R : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    ask : M R;
    ask_ask : ask >> ask = ask;
}.

#[global] Hint Rewrite @ask_ask : CoqMTL.

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

(** Interestingly, we can prove that if the base monad [M] has an instance
    of [MonadReader], then a monad transformer fed with [M] also has an
    instance of [MonadReader]. This is impossible with the other classes. *)
#[refine]
#[export]
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