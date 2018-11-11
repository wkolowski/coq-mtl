Require Import Control.

Require Import HSLib.Instances.Identity.

Definition Free (F : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> X) -> (F X -> X) -> X.

Section Free.

Variable F : Type -> Type.

Definition fmap_Free
  {A B : Type} (f : A -> B) (x : Free F A) : Free F B :=
    fun X pure free => x X (f .> pure) free.

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
    fun X pure free => mf X (fun f => fmap f ma X pure free) free.

Instance Applicative_Free : Applicative (Free F) :=
{
    pure := @pure_Free;
    ap := @ap_Free;
}.
Proof. all: reflexivity. Defined.

Definition bind_Free
  {A B : Type} (x : Free F A) (f : A -> Free F B) : Free F B :=
    fun X pure free => x X (fun a => f a X pure free) free.

Instance Monad_Free : Monad (Free F) :=
{
    bind := @bind_Free
}.
Proof. all: reflexivity. Defined.

End Free.

Theorem Free_not_Alternative :
  (forall F : Type -> Type, Alternative (Free F)) -> False.
Proof.
  unfold Free; intro. destruct (X Identity); unfold Identity in *.
  apply (aempty False False); trivial.
Qed.

Theorem Free_not_MonadPlus :
  (forall F : Type -> Type, MonadPlus (Free F)) -> False.
Proof.
  intro. apply Free_not_Alternative, X.
Defined.

Class MonadFree
  (F M : Type -> Type) (instF : Functor F) (instM : Monad M) : Type :=
{
    wrap : forall {A : Type}, F (M A) -> M A;
    wrap_law :
      forall (A B : Type) (f : A -> M B) (x : F A),
        wrap (fmap f x) = wrap (@fmap F instF _ _ pure x) >>= f
}.

Definition wrap_Free
  {F : Type -> Type} {A : Type} (x : Free F (Free F A)) : Free F A :=
    fun X pure free =>
      x X (fun f : forall X : Type, (A -> X) -> (F X -> X) -> X =>
               f X pure free)
        free.

Instance MonadFree_Free
  (F : Type -> Type) (inst : Functor F)
  : MonadFree (Free F) (Free F) (Functor_Free F) (Monad_Free F) :=
{
    wrap := @wrap_Free F;
}.
Proof. hs. Defined.

Hint Unfold Free fmap_Free pure_Free ap_Free bind_Free wrap_Free.