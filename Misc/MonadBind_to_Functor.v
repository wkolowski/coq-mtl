Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Applicative.Applicative.
Require Export HSLib.Functor.Functor.

Class Monad (M : Type -> Type) : Type :=
{
    ret : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_ret_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (ret a) f = f a;
    bind_ret_r :
      forall (A : Type) (ma : M A),
        bind ma ret = ma;
    assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
}.

Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).

Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).

End MonadNotations.

Export MonadNotations.

Hint Rewrite @bind_ret_l @bind_ret_r @assoc : monad_laws.

Ltac monad' :=
  intros;
  autorewrite with monad_laws;
  autorewrite with applicative_laws.

Ltac monad :=
repeat (monad'; repeat match goal with
    | H : _ * _ |- _ => destruct H
    | |- ?x >>= _ = ?x => rewrite <- bind_ret_r
    | |- ?x = ?x >>= _ => rewrite <- bind_ret_r at 1
    | |- ?x >>= _ = ?x >>= _ => f_equal
    | |- (fun _ => _) = _ => let x := fresh "x" in ext x
    | |- _ = (fun _ => _) => let x := fresh "x" in ext x
    | |- context [match ?x with _ => _ end] => destruct x
end; monad'); try (unfold compose, id; cbn; congruence; fail).

Definition fmap_Monad
  {M : Type -> Type} {inst : Monad M}
  {A B : Type} (f : A -> B) (ma : M A) : M B :=
    ma >>= (f .> ret).

Instance Functor_Monad
  (M : Type -> Type) (inst : Monad M) : Functor M :=
{
    fmap := @fmap_Monad M inst;
}.
Proof.
  all: unfold fmap_Monad, compose; monad.
Defined.