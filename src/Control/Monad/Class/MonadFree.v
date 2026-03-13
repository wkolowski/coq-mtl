From CoqMTL Require Export Control.Monad.

(** A class that represents a free monad of a functor [F]. *)
Class MonadFree
  (F M : Type -> Type) (instF : Functor F) (instM : Monad M) : Type :=
{
  wrap : forall {A : Type}, F (M A) -> M A;
  wrap_law :
    forall (A B : Type) (f : A -> M B) (x : F A),
      wrap (fmap f x) = wrap (@fmap F instF _ _ pure x) >>= f
}.

(** There's no rewrite hint for [wrap_law], because it can be rewritten
    ad infinitum, so [autorewrite] would loop. *)