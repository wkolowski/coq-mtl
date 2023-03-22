From CoqMTL Require Import Control.Applicative.

Class Monad (M : Type -> Type) : Type :=
{
  is_applicative :> Applicative M;
  compM : forall {A B C : Type}, (A -> M B) -> (B -> M C) -> (A -> M C);
  compM_pure_l :
    forall (A B : Type) (f : A -> M B), compM pure f = f;
  compM_pure_r :
    forall (A B : Type) (f : A -> M B), compM f pure = f;
  compM_assoc :
    forall (A B C D : Type) (f : A -> M B) (g : B -> M C) (h : C -> M D),
      compM f (compM g h) = compM (compM f g) h;
(*
  compM_const :
    forall (A B C : Type) (f : B -> M C) (a : A) (b : B),
      (compM (fun _ : A => pure b) f) a = f b;
*)
}.

Coercion is_applicative : Monad >-> Applicative.

Notation "f >=> g" := (compM f g) (at level 40).

Definition bindM
  {M : Type -> Type} {inst : Monad M}
  {A B : Type} (x : M A) (f : A -> M B) : M B :=
    compM (fun _ : unit => x) f tt.

Lemma bind_ap :
  forall
    (M : Type -> Type) (inst : Monad M) (A B : Type)
    (mf : M (A -> B)) (mx : M A),
        mf <*> mx = bindM mf (fun f => bindM mx (fun x => pure (f x))).
Proof.
  intros. unfold bindM.
Abort.

#[global] Hint Unfold bindM : CoqMTL.

From CoqMTL Require MonadBind.

(*
#[refine]
#[export]
Instance Comp_to_Bind
  (M : Type -> Type) (inst : Monad M) : MonadBind.Monad M :=
{
  bind := @bindM M inst;
  pure := @pure M inst
}.
Proof.
  all: unfold bindM; cbn; intros.
    rewrite compM_const. reflexivity.
    rewrite compM_pure_r. reflexivity.
    replace (fun x : A => ((fun _ : unit => f x) >=> g) tt)
       with (f >=> g).
      Focus 2. ext x. rewrite compM_const.
      rewrite compM_assoc.

Abort.
*)