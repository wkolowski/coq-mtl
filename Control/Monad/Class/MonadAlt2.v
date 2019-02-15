Require Import HSLib.Base.
Require Import Control.Monad.
Require Import Control.Alternative.
Require Import Control.Foldable.

Class MonadAltR (M : Type -> Type) (inst : Monad M) : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    choose_bind_r :
      forall (A B : Type) (m : M A) (f g : A -> M B),
        (m >>= fun x : A => choose (f x) (g x)) =
        choose (m >>= f) (m >>= g)
}.

Hint Rewrite @choose_assoc @choose_bind_r : HSLib.