Require Import HSLib.Base.

Class Monad (M : Type -> Type) : Type :=
{
    pure : forall {A : Type}, A -> M A;
    compM : forall {A B C : Type}, (A -> M B) -> (B -> M C) -> (A -> M C);
    compM_pure_l :
      forall (A B : Type) (f : A -> M B), compM pure f = f;
    compM_pure_r :
      forall (A B : Type) (f : A -> M B), compM f pure = f;
    compM_assoc :
      forall (A B C D : Type) (f : A -> M B) (g : B -> M C) (h : C -> M D),
        compM f (compM g h) = compM (compM f g) h;
}.

Notation "f >=> g" := (compM f g) (at level 40).

Definition bindM
  (M : Type -> Type) (inst : Monad M)
  {A B : Type} (x : M A) (f : A -> M B) : M B :=
    compM (fun _ : unit => x) f tt.

Hint Unfold bindM : HSLib.

Require MonadBind.

Instance Comp_to_Bind
  (M : Type -> Type) (inst : Monad M) : MonadBind.Monad M :=
{
    bind := @bindM M inst;
    pure := @pure M inst
}.
Proof.
  all: MonadBind.monad.
    Focus 3. compute. destruct inst. cbn.
Abort.