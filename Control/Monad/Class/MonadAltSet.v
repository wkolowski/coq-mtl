Require Export Control.Monad.

(** A nondeterministic choice monad whose initial model are finite sets.
    This is guaranteed by the laws [choose_comm] and [choose_idempotent]. *)
Class MonadAltSet (M : Type -> Type) (inst : Monad M) : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    choose_comm :
      forall {A : Type} (x y : M A),
        choose x y = choose y x;
    choose_idempotent :
      forall {A : Type} (x : M A), choose x x = x
}.

#[global] Hint Rewrite @choose_assoc @choose_comm @choose_idempotent : CoqMTL.