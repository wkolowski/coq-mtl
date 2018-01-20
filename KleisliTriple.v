Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.Functor.Functor.
Require Export HSLib.Applicative.Applicative.

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

Hint Rewrite @eta_star @star_eta @star_comp : Kleisli.
Hint Rewrite @eta_star @star_eta : Kleisli'.
Hint Rewrite <- @star_comp : Kleisli'.

Ltac ktl := autorewrite with Kleisli.
Ltac ktr := autorewrite with Kleisli'.

Ltac kt := ktl + ktr; congruence + reflexivity.

Require Import HSLib.MonadBind.Monad.

Section KleisliTriple_to_MonadBind.

Variable M : Type -> Type.
Variable inst : KleisliTriple M.

Definition fmap_Kleisli
  {A B : Type} (f : A -> B) : M A -> M B := star (f .> eta).

Instance Functor_Kleisli : Functor M :=
{
    fmap := @fmap_Kleisli
}.
Proof.
  all: unfold fmap_Kleisli; intros.
    rewrite id_left. ext x. kt.
    ext x. unfold compose. ktr. unfold compose.
    f_equal. ext a. kt.
Defined.

Definition ret_Kleisli {A : Type} : A -> M A := eta.

Definition bind_Kleisli
  {A B : Type} : M A -> (A -> M B) -> M B := flip star.

Definition ap_Kleisli {A B : Type} (mf : M (A -> B)) (ma : M A) : M B :=
  bind_Kleisli mf (fun f =>
  bind_Kleisli ma (fun a =>
    ret_Kleisli (f a))).

Instance Applicative_Kleisli : Applicative M :=
{
    ret := @ret_Kleisli;
    ap := @ap_Kleisli;
}.
Proof.
  all: unfold fmap_Kleisli, ap_Kleisli, bind_Kleisli, ret_Kleisli, flip;
  cbn; intros; try kt.
    ktl. ktr. unfold compose. f_equal. ext bc. ktr. f_equal. ext ab.
      unfold compose. ktr. f_equal. ext a. unfold compose. kt.
    ktl. f_equal. ext ab. kt.
Defined.

Instance Monad_KleisliTriple : Monad M :=
{
    bind := @bind_Kleisli;
}.
Proof.
  all: unfold fmap_Kleisli, ap_Kleisli, bind_Kleisli, ret_Kleisli, flip;
  cbn; intros; try kt.
Defined.

End KleisliTriple_to_MonadBind.

Section MonadBind_to_KleisliTriple.

Variable M : Type -> Type.
Variable inst : Monad M.

Definition eta_Monad := @ret M inst.

Definition star_Monad {A B : Type} := flip (@bind M inst A B).

Instance KleisliTriple_Monad : KleisliTriple M :=
{
    eta := @eta_Monad;
    star := @star_Monad;
}.
Proof.
  all: unfold eta_Monad, star_Monad, flip; monad.
Defined.

End MonadBind_to_KleisliTriple.