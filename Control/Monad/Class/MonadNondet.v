Require Export Control.Monad.Class.MonadFail.
Require Export Control.Monad.Class.MonadAlt.

(** Nondeterminism monad. We have failure and nondeterministic choice.
    The laws can be summarized by saying that if we can choose, we
    don't choose failure. *)
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

Hint Rewrite @choose_fail_l @choose_fail_r : HSLib.