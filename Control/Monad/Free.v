Require Import Control.All.
Require Import Control.Monad.Identity.
Require Import Control.Monad.Class.MonadFree.

(** The free monad of a functor F. It models a computation whose effects
    are described by the functor F. Contrary to Haskell, it is implemented
    using Church encoding, because the corresponding inductive type is not
    strictly positive.

    The implementation is type-driven, so we shouldn't expect to get an
    intuitive understanding of what the operations really do... *)

Definition Free (F : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> X) -> (F X -> X) -> X.

Section Free.

Variable F : Type -> Type.

Definition fmap_Free
  {A B : Type} (f : A -> B) (x : Free F A) : Free F B :=
    fun X pure wrap => x X (f .> pure) wrap.

#[refine]
Instance Functor_Free : Functor (Free F) :=
{
    fmap := @fmap_Free
}.
Proof. all: reflexivity. Defined.

Definition pure_Free
  {A : Type} (x : A) : Free F A :=
    fun X pure _ => pure x.

Definition ap_Free
  {A B : Type} (mf : Free F (A -> B)) (ma : Free F A) : Free F B :=
    fun X pure wrap => mf X (fun f => fmap f ma X pure wrap) wrap.

#[refine]
Instance Applicative_Free : Applicative (Free F) :=
{
    pure := @pure_Free;
    ap := @ap_Free;
}.
Proof. all: reflexivity. Defined.

Definition bind_Free
  {A B : Type} (x : Free F A) (f : A -> Free F B) : Free F B :=
    fun X pure wrap => x X (fun a => f a X pure wrap) wrap.

#[refine]
Instance Monad_Free : Monad (Free F) :=
{
    bind := @bind_Free
}.
Proof. all: reflexivity. Defined.

End Free.

(** We shouldn't expect free monads to support any structure besides that
    of a monad, so in particular no [Alternative]. *)
Lemma Free_not_Alternative :
  (forall F : Type -> Type, Alternative (Free F)) -> False.
Proof.
  unfold Free; intro. destruct (X Identity); unfold Identity in *.
  apply (aempty False False); trivial.
Qed.

Definition wrap_Free
  {F : Type -> Type} {instF : Functor F} {A : Type}
  (x : F (Free F A)) : Free F A :=
    fun X pure wrap =>
      wrap (fmap (fun f : forall X : Type, (A -> X) -> (F X -> X) -> X =>
               f X pure wrap) x).

Global Hint Unfold fmap_Free pure_Free ap_Free bind_Free wrap_Free : CoqMTL.

#[refine]
Instance MonadFree_Free
  (F : Type -> Type) (instF : Functor F)
  : MonadFree F (Free F) instF (Monad_Free F) :=
{
    wrap := @wrap_Free F instF
}.
Proof.
  monad. rewrite <- !fmap_comp'. unfold compose. reflexivity.
Defined.