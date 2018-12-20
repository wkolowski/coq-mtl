Require Import Control.Monad.

Class CommutativeMonad (M : Type -> Type) : Type :=
{
    is_monad : Monad M;
    bind_comm :
      forall (A B C : Type) (x : M A) (y : M B) (f : A -> B -> M C),
        x >>= (fun a : A => y >>= fun b : B => f a b) =
        y >>= (fun b : B => x >>= fun a : A => f a b)
}.

