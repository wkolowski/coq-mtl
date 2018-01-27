Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Applicative.
Require Export Control.Functor.

(* Definition of monad using bind (monadic application). *)
Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    pure : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_pure_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (pure a) f = f a;
    bind_pure_r :
      forall (A : Type) (ma : M A),
        bind ma pure = ma;
    assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
    fmap_bind_pure :
      forall (A B : Type) (f : A -> B) (x : M A),
        fmap f x = bind x (fun a : A => pure (f a));
}.

Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).

Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).

End MonadNotations.

Export MonadNotations.

Hint Rewrite @bind_pure_l @bind_pure_r @assoc @fmap_bind_pure : HSLib.

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

Definition ap_Monad
  (M : Type -> Type) (inst : Monad M)
  (A B : Type) (mf : M (A -> B)) (ma : M A) : M B :=
    bind mf (fun f => bind ma (fun a => pure (f a))).

Instance Monad_Applicative
  (M : Type -> Type) (inst : Monad M) : Applicative M :=
{
    pure := @pure M inst;
    ap := ap_Monad M inst;
}.
Proof.
  all: cbn; unfold ap_Monad; monad.
Defined.

Section wut.

Variable M : Type -> Type.
Variable inst : Monad M.

Definition wut : Prop :=
  forall (A B : Type) (f : A -> B) (x : M A),
    fmap f x = x >>= (fun a : A => pure (f a)).

Definition bind_fmap_wut : Prop :=
  forall (A B C : Type) (f : A -> B) (x : M A) (g : B -> M C),
    bind (fmap f x) g = bind x (f .> g).

Definition fmap_bind_wut : Prop :=
  forall (A B C : Type) (x : M A) (f : A -> M B) (g : B -> C),
    fmap g (bind x f) = bind x (fun x0 : A => fmap g (f x0)).

Lemma bind_ap_derived :
  forall (A B : Type) (mf : M (A -> B)) (mx : M A),
    mf <*> mx = bind mf (fun f => bind mx (fun x => pure (f x))).
Proof.
  intros.
  replace (fun f : A -> B => mx >>= (fun x : A => pure (f x)))
  with (fun f : A -> B => fmap f mx).
    Focus 2. monad.
Abort.

End wut.