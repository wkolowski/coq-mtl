Require Export Control.Monad.

(** A nondeterminism monad whose initial model are finite bags
    (which probably means finite multisets). This is guaranteed
    by the law [choose_comm]. *)
Class MonadAltBag (M : Type -> Type) (inst : Monad M) : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    choose_comm :
      forall {A : Type} (x y : M A),
        choose x y = choose y x
}.

#[global] Hint Rewrite @choose_assoc @choose_comm : CoqMTL.