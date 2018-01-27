Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Control.Monad.

Class MonadTrans (T : (Type -> Type) -> Type -> Type) : Type :=
{
    is_monad : forall (M : Type -> Type), Monad M -> Monad (T M);
    lift : forall {M : Type -> Type} {_inst : Monad M} {A : Type},
      M A -> T M A;
    lift_pure :
      forall (M : Type -> Type) {_inst : Monad M} (A : Type) (x : A),
        lift (pure x) = pure x;
    lift_bind :
      forall {M : Type -> Type} {_inst : Monad M} (A B : Type) (x : M A)
        (f : A -> M B), lift (x >>= f) = lift x >>= (f .> lift)
}.

(* Tactic for dealing with functor instances specific to monad
   transformers. *)
Ltac mtrans := hs; try
match goal with
    | |- fmap (fun x : ?A => ?e) = _ =>
          let x := fresh "x" in
          replace (fun x : A => e) with (@id A);
          [rewrite fmap_id | ext x; induction x]; try reflexivity
    | |- context [fmap ?f = fmap ?g .> fmap ?h] =>
          let x := fresh "x" in
          replace f with (g .> h);
          [rewrite fmap_comp | ext x; induction x]; try reflexivity
    | |- context [fmap ?f = fun _ => fmap ?g (fmap ?h _)] =>
          let x := fresh "x" in ext x;
          rewrite <- fmap_comp'; f_equal
end.