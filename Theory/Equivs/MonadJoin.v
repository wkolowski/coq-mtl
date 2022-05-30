From CoqMTL Require Export Control.Applicative.

Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
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
    join_ap :
      forall (A B : Type) (mf : M (A -> B)) (ma : M A),
        mf <*> ma =
        join (pure (fun f : A -> B => join (fmap (f .> pure) ma)) <*> mf)
}.

Coercion is_applicative : Monad >-> Applicative.

#[global] Hint Rewrite
  @join_fmap_join @join_pure @join_fmap_pure @join_fmap_fmap : MonadJoin.

#[global] Hint Rewrite <- @join_ap : MonadJoin.

Definition bind
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (ma : M A) (f : A -> M B) : M B := (fmap f .> join) ma.

Definition compM
  {A B C : Type} {M : Type -> Type} {inst : Monad M}
  (f : A -> M B) (g : B -> M C) : A -> M C :=
    f .> fmap g .> join.

#[global] Hint Unfold bind compM compose : MonadJoin.

Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).

End MonadNotations.

Export MonadNotations.

Ltac mjoin :=
  repeat (intros;
    autounfold with MonadJoin CoqMTL;
    autorewrite with MonadJoin CoqMTL;
    f_equal; exts; try reflexivity).

Lemma assoc :
  forall
    (M : Type -> Type) (inst : Monad M)
    (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
      bind (bind ma f) g = bind ma (fun x => bind (f x) g).
Proof.
  unfold bind, compose; intros.
  rewrite <- !join_fmap_fmap.
  change (fun x : A => join (fmap g (f x))) with (f .> fmap g .> join).
  rewrite !fmap_comp. unfold compose. rewrite join_fmap_join.
  reflexivity.
Qed.