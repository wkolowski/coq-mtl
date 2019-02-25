Require Export HSLib.Control.Monad.

(** Haskell-style monad transformers. The categorical semantics is not yet
    clear to me (a monad morphism?, a natural transformation preserving the
    [Applicative]/[Monad] structure?).

    The laws are standard, taken from Haskell's standard library. *)
Class MonadTrans (T : (Type -> Type) -> Type -> Type) : Type :=
{
    is_monad : forall (M : Type -> Type), Monad M -> Monad (T M);
    lift :
      forall {M : Type -> Type} {_inst : Monad M} {A : Type}, M A -> T M A;
    lift_pure :
      forall (M : Type -> Type) {_inst : Monad M} (A : Type) (x : A),
        lift (pure x) = pure x;
    lift_bind :
      forall {M : Type -> Type} {_inst : Monad M} (A B : Type) (x : M A)
        (f : A -> M B), lift (x >>= f) = lift x >>= (f .> lift)
}.

(** A tactic for dealing with functor instances specific to monad
    transformers. *)
Ltac mtrans := hs; try
match goal with
    | |- fmap (fun x : ?A => ?e) = _ =>
          let x := fresh "x" in
          replace (fun x : A => e) with (@id A);
          [rewrite fmap_id | ext x; destruct x]; try reflexivity
    | |- context [fmap ?f = fmap ?g .> fmap ?h] =>
          let x := fresh "x" in
          replace f with (g .> h);
          [rewrite fmap_comp | ext x; destruct x]; try reflexivity
    | |- context [fmap ?f = fun _ => fmap ?g (fmap ?h _)] =>
          let x := fresh "x" in ext x;
          rewrite <- fmap_comp'; f_equal
end.

Lemma lift_constrA :
  forall
    (T : (Type -> Type) -> Type -> Type) (instT : MonadTrans T)
    (M : Type -> Type) (instM : Monad M)
    (A B : Type) (x : M A) (y : M B),
      @constrA (T M) (is_monad _ instM) _ _ (lift x) (lift y) =
      @lift T instT M instM B (x >> y).
Proof.
  intros.
    rewrite !constrA_spec.
    rewrite lift_bind. unfold compose. reflexivity.
Defined.