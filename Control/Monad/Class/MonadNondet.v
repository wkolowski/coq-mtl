Require Export Control.Monad.Class.MonadFail.
Require Export Control.Monad.Class.MonadAlt.

(** A monad that represents nondeterministic computations, i.e. ones that can
    [fail] and make choices. The laws can be summarized by saying that if we
    can choose, we don't choose failure. *)
Class MonadNondet (M : Type -> Type) (inst : Monad M) : Type :=
{
    instF :> MonadFail M inst;
    instA :> MonadAlt M inst;
    choose_fail_l :
      forall (A : Type) (x : M A),
        choose fail x = x;
    choose_fail_r :
      forall (A : Type) (x : M A),
        choose x fail = x;
}.

Coercion instF : MonadNondet >-> MonadFail.
Coercion instA : MonadNondet >-> MonadAlt.

#[global] Hint Rewrite @choose_fail_l @choose_fail_r : CoqMTL.