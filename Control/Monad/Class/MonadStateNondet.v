Require Export Control.Monad.Class.MonadNondet.
Require Export Control.Monad.Class.MonadState.

(** A monad that models both nondeterministic and stateful computations.
    The law [seq_fail_r] says that eventual failure makes the whole
    computation fail. [bind_choose_r] says that if a choice depends on
    a previous computation, it can be expressed as a more complicated
    choice. They can probably be summed up by saying that the state is
    local to each branch of nondeterminism.
*)
Class MonadStateNondet
  (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    instS :> MonadState S M inst;
    instN :> MonadNondet M inst;
    seq_fail_r :
      forall (A B : Type) (x : M A),
        x >> fail = @fail M inst instN B;
    bind_choose_r :
      forall (A B : Type) (f g : A -> M B) (ma : M A),
        ma >>= (fun x : A => choose (f x) (g x)) =
        choose (ma >>= f) (ma >>= g)
}.

Coercion instS : MonadStateNondet >-> MonadState.
Coercion instN : MonadStateNondet >-> MonadNondet.

#[global] Hint Rewrite @seq_fail_r @bind_choose_r : CoqMTL.