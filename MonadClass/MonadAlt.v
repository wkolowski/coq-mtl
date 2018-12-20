Require Import HSLib.Base.
Require Import Control.Monad.

Class MonadAlt (M : Type -> Type) (inst : Monad M) : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    choose_bind :
      forall (A B : Type) (x y : M A) (f : A -> M B),
        choose x y >>= f = choose (x >>= f) (y >>= f);
}.