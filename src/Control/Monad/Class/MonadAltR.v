From CoqMTL Require Export Control.Monad.

(** Another monad for nondeterministic choice, but it satisfies a different
    law than [MonadAlt]. *)
Class MonadAltR (M : Type -> Type) (inst : Monad M) : Type :=
{
  choose : forall {A : Type}, M A -> M A -> M A;
  choose_assoc :
    forall {X : Type} (a b c : M X),
      choose (choose a b) c = choose a (choose b c);
  bind_choose_r :
    forall (A B : Type) (m : M A) (f g : A -> M B),
      m >>= (fun x : A => choose (f x) (g x)) =
      choose (m >>= f) (m >>= g)
}.

#[global] Hint Rewrite @choose_assoc @bind_choose_r : CoqMTL.