Require Import HSLib.Base.
Require Import Control.Monad.

(** The initial model are finite bags
    (which probably means finite multisets). *)
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