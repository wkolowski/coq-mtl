Require Import HSLib.Base.
Require Import Control.Monad.

Class MonadFree
  (F M : Type -> Type) (instF : Functor F) (instM : Monad M) : Type :=
{
    wrap : forall {A : Type}, F (M A) -> M A;
    wrap_law :
      forall (A B : Type) (f : A -> M B) (x : F A),
        wrap (fmap f x) = wrap (@fmap F instF _ _ pure x) >>= f
}.

(*
Hint Rewrite @wrap_law : HSLib.
*)