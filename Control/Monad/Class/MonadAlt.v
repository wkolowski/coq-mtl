From CoqMTL Require Export Control.Monad.

(** A monad that models computations which can perform some kind of choice.
    It may be thought of as nondeterministic choice, which is quite intuitive
    from the law [bind_choose_l]. *)
Class MonadAlt (M : Type -> Type) (inst : Monad M) : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    bind_choose_l :
      forall (A B : Type) (x y : M A) (f : A -> M B),
        choose x y >>= f = choose (x >>= f) (y >>= f);
}.

#[global] Hint Rewrite @choose_assoc @bind_choose_l : CoqMTL.