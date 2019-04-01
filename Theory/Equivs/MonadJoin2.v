Require Export Control.Applicative.

Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    pure : forall {A : Type}, A -> M A;
    join : forall {A : Type}, M (M A) -> M A;
    join_fmap_join :
      forall (A : Type) (x : M (M (M A))),
        join (fmap join x) = join (join x);
    join_pure :
      forall (A : Type) (ma : M A), join (pure ma) = ma;
    join_fmap_pure :
      forall (A : Type) (x : M A),
        join (fmap pure x) = x;
    join_fmap_fmap :
      forall (A B : Type) (f : A -> B) (x : M (M A)),
        join (fmap (fmap f) x) = fmap f (join x);
}.

Coercion is_functor : Monad >-> Functor.

Hint Rewrite @join_fmap_join @join_pure @join_fmap_pure @join_fmap_fmap
  : join.

Definition bind
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (ma : M A) (f : A -> M B) : M B := (fmap f .> join) ma.

Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).

End MonadNotations.

Export MonadNotations.

Definition ap
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mf : M (A -> B)) (mx : M A) : M B :=
    mf >>= fun f =>
    mx >>= fun x => pure (f x).

Instance Applicative_Monad
  (M : Type -> Type) (inst : Monad M) : Applicative M :=
{
    pure := @pure M inst;
    ap := @ap M inst;
}.
Proof.
  unfold ap, bind, compose; intros.
    rewrite join_fmap_fmap.
    autorewrite with join.