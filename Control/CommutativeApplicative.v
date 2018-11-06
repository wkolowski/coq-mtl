Require Export HSLib.Control.Applicative.

(** An applicative functor is commutative if its [ap]'s arguments can be
    evaluated in any order. The intended categorical semantics is therefore
    strong commutative monoidal functor. *)
Class CommutativeApplicative
  (F : Type -> Type) (inst : Applicative F) : Prop :=
{
    ap_comm :
      forall (A B C : Type) (f : A -> B -> C) (u : F A) (v : F B),
        f <$> u <*> v = flip f <$> v <*> u
}.