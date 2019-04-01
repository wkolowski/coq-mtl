Require Import Control.Applicative.

Class Monad (M : Type -> Type) : Type :=
{
    pure : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_pure_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (pure a) f = f a;
    bind_pure_r :
      forall (A : Type) (ma : M A),
        bind ma pure = ma;
    bind_assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
}.

Notation "mx >>= f" := (bind mx f) (at level 40).

Hint Rewrite @bind_pure_l @bind_pure_r @bind_assoc : HSLib.

Ltac monad :=
repeat (hs; repeat match goal with
    | H : _ * _ |- _ => destruct H
    | |- ?x >>= _ = ?x => rewrite <- bind_pure_r
    | |- ?x = ?x >>= _ => rewrite <- bind_pure_r at 1
    | |- ?x >>= _ = ?x >>= _ => f_equal
    | |- (fun _ => _) = _ => let x := fresh "x" in ext x
    | |- _ = (fun _ => _) => let x := fresh "x" in ext x
    | |- context [match ?x with _ => _ end] => destruct x
end; hs); try (unfold compose, id; cbn; congruence; fail).

Definition fmap_MonadBind
  {M : Type -> Type} {inst : Monad M}
  {A B : Type} (f : A -> B) (ma : M A) : M B :=
    ma >>= (f .> pure).

Hint Unfold fmap_MonadBind compose : HSLib.

Instance Functor_MonadBind
  (M : Type -> Type) (inst : Monad M) : Functor M :=
{
    fmap := @fmap_MonadBind M inst;
}.
Proof. unfold fmap_MonadBind, compose, id. all: monad. Defined.

Definition ap_MonadBind
  (M : Type -> Type) (inst : Monad M)
  (A B : Type) (mf : M (A -> B)) (ma : M A) : M B :=
    bind mf (fun f => bind ma (fun a => pure (f a))).

Hint Unfold ap_MonadBind : HSLib.

Instance Applicative_MonadBind
  (M : Type -> Type) (inst : Monad M) : Applicative M :=
{
    pure := @pure M inst;
    ap := @ap_MonadBind M inst;
}.
Proof. all: monad. Defined.

Section DerivedLaws.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Lemma fmap_bind_pure :
  forall (A B : Type) (f : A -> B) (x : M A),
    fmap f x = x >>= (fun a : A => pure (f a)).
Proof. monad. Qed.

Lemma bind_ap :
  forall (A B : Type) (mf : M (A -> B)) (mx : M A),
    mf <*> mx = bind mf (fun f => bind mx (fun x => pure (f x))).
Proof. monad. Qed.

End DerivedLaws.