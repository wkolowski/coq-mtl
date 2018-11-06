Require Import Control.

Definition RoseTreeT (M : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> M X) -> (M X -> M X -> M X) -> M X.

Section wut.

Variable M : Type -> Type.
Variable inst : Monad M.

Definition fmap_RoseTreeT
  {A B : Type} (f : A -> B) (t : RoseTreeT M A) : RoseTreeT M B :=
    fun X leaf node => t X (f .> leaf) node.

Instance Functor_RoseTreeT : Functor (RoseTreeT M) :=
{
    fmap := @fmap_RoseTreeT
}.
Proof.
  all: reflexivity.
Defined.

Definition pure_RoseTreeT
  {A : Type} (x : A) : RoseTreeT M A :=
    fun X leaf _ => leaf x.

Definition ap_RoseTreeT
  {A B : Type} (tf : RoseTreeT M (A -> B)) (ta : RoseTreeT M A)
  : RoseTreeT M B := fun X leaf node =>
    tf X (fun f => fmap f ta X leaf node) node.

Instance Applicative_RoseTreeT : Applicative (RoseTreeT M) :=
{
    pure := @pure_RoseTreeT;
    ap := @ap_RoseTreeT;
}.
Proof.
  all: reflexivity.
Defined.

Definition bind_RoseTreeT
  {A B : Type} (ta : RoseTreeT M A) (tf : A -> RoseTreeT M B)
  : RoseTreeT M B := fun X leaf node =>
    ta X (fun a => tf a X leaf node) node.

Instance Monad_RoseTreeT : Monad (RoseTreeT M) :=
{
    bind := @bind_RoseTreeT
}.
Proof.
  all: reflexivity.
Defined.

End wut.

Theorem RoseTreeT_not_Alternative :
  (forall (M : Type -> Type) (inst : Monad M), Alternative (RoseTreeT M)) ->
  False.
Proof.
  unfold RoseTreeT; intros.
  Require Import HSLib.Instances.All.
  
  specialize (X Identity (MonadIdentity)).
  unfold Identity in *. destruct X.
  apply (aempty False False); trivial.
Qed.

Theorem RoseTreeT_not_MonadPlus :
  (forall (M : Type -> Type) (inst : Monad M), MonadPlus (RoseTreeT M)) ->
  False.
Proof.
  intros. apply RoseTreeT_not_Alternative, X.
Qed.