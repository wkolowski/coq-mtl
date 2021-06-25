Require Import Control.Monad.

(** This looks identical to MonadBind. *)
Class KleisliTriple (M : Type -> Type) : Type :=
{
    eta : forall {A : Type}, A -> M A;
    star : forall {A B : Type}, (A -> M B) -> M A -> M B;
    eta_star :
      forall (A B : Type) (f : A -> M B) (x : A),
        star f (eta x) = f x;
    star_eta :
      forall (A : Type) (x : M A),
        star eta x = x;
    star_comp :
      forall (A B C : Type) (f : A -> M B) (g : B -> M C) (x : M A),
        star (f .> star g) x = star g (star f x)
}.

Hint Rewrite @eta_star @star_eta : Kleisli.
Hint Rewrite <- @star_comp : Kleisli.

Ltac kleisli :=
  repeat (
    cbn; intros;
    autounfold with Kleisli;
    autorewrite with Kleisli;
    f_equal; exts; try reflexivity).

Section KleisliTriple_Instances.

Variable M : Type -> Type.
Variable inst : KleisliTriple M.

Definition fmap_Kleisli
  {A B : Type} (f : A -> B) : M A -> M B := star (f .> eta).

Hint Unfold fmap_Kleisli compose : Kleisli.

#[refine]
Instance Functor_Kleisli : Functor M :=
{
    fmap := @fmap_Kleisli
}.
Proof. all: kleisli. Defined.

Definition pure_Kleisli {A : Type} : A -> M A := eta.

Definition bind_Kleisli
  {A B : Type} : M A -> (A -> M B) -> M B := flip star.

Definition ap_Kleisli {A B : Type} (mf : M (A -> B)) (ma : M A) : M B :=
  bind_Kleisli mf (fun f =>
  bind_Kleisli ma (fun a =>
    pure_Kleisli (f a))).

Hint Unfold pure_Kleisli bind_Kleisli ap_Kleisli flip : Kleisli.

#[refine]
Instance Applicative_Kleisli : Applicative M :=
{
    pure := @pure_Kleisli;
    ap := @ap_Kleisli;
}.
Proof. all: kleisli. Defined.

End KleisliTriple_Instances.

Global Hint Unfold
  fmap_Kleisli pure_Kleisli bind_Kleisli ap_Kleisli compose flip : Kleisli.