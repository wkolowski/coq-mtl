Require Import Control.

Require Import HSLib.Instances.Identity.

Definition FreeT (F : Type -> Type) (M : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> M X) -> (F X -> M X) -> M X.

Section FreeT.

Variables
  (F : Type -> Type)
  (M : Type -> Type)
  (inst : Monad M).

Definition fmap_FreeT
  {A B : Type} (f : A -> B) (x : FreeT F M A) : FreeT F M B :=
    fun X pure free => x X (f .> pure) free.

Instance Functor_FreeT : Functor (FreeT F M) :=
{
    fmap := @fmap_FreeT
}.
Proof. all: reflexivity. Defined.

Definition pure_FreeT
  {A : Type} (x : A) : FreeT F M A :=
    fun X pure _ => pure x.

Definition ap_FreeT
  {A B : Type} (mf : FreeT F M (A -> B)) (ma : FreeT F M A) : FreeT F M B :=
    fun X pure free => mf X (fun f => fmap f ma X pure free) free.

Instance Applicative_FreeT : Applicative (FreeT F M) :=
{
    pure := @pure_FreeT;
    ap := @ap_FreeT;
}.
Proof. all: reflexivity. Defined.

Definition bind_FreeT
  {A B : Type} (x : FreeT F M A) (f : A -> FreeT F M B) : FreeT F M B :=
    fun X pure free => x X (fun a => f a X pure free) free.

Instance Monad_FreeT : Monad (FreeT F M) :=
{
    bind := @bind_FreeT
}.
Proof. all: reflexivity. Defined.

End FreeT.

Theorem FreeT_not_Alternative :
  (forall (F : Type -> Type) (M : Type -> Type) (inst : Monad M),
    Alternative (FreeT F M)) -> False.
Proof.
  intro H. destruct (H Identity Identity _).
  unfold FreeT, Identity in *.
  apply (aempty False False); trivial.
Qed.

Theorem FreeT_not_MonadPlus :
  (forall (F : Type -> Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (FreeT F M)) -> False.
Proof.
  intro. apply FreeT_not_Alternative, X.
Qed.

Definition lift_FreeT
  {F M : Type -> Type} {inst : Monad M} {A : Type}
  (x : M A) : FreeT F M A :=
    fun X pure free =>
      x >>= fun a : A => pure a.

Hint Unfold lift_FreeT : HSLib.

Instance MonadTrans_FreeT
  {F : Type -> Type} : MonadTrans (FreeT F) :=
{
    is_monad := fun M _ => @Monad_FreeT F M;
    lift := @lift_FreeT F;
}.
Proof. all: monad. Defined.