Require Export Control.Monad.Class.MonadNondet.
Require Export Control.Monad.Class.MonadState.

(** A monad that models both nondeterministic and stateful computations.
    
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

Hint Rewrite @seq_fail_r @bind_choose_r : HSLib.