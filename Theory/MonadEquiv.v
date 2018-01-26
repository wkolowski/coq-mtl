Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.

Module Join.
Require Import HSLib.MonadJoin.Monad.
Include HSLib.MonadJoin.Monad.
End Join.

Module Bind.
Require Import Control.Monad.
Include Control.Monad.
End Bind.

Require Import Control.Applicative.
Require Import HSLib.Misc.KleisliTriple.

Instance JoinToBind
  (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_applicative := @Join.is_applicative M inst;
    bind := @Join.bind M inst
}.
Proof.
  apply Join.bind_ret_l.
  apply Join.bind_ret_r.
  apply Join.assoc.
  apply Join.fmap_bind_ret.
  apply Join.bind_ap.
Defined.

Instance BindToComp (M : Type -> Type) (inst : Bind.Monad M)
  : Comp.Monad M :=
{
    is_applicative := @Bind.is_applicative M inst;
    compM := @Bind.compM M inst
}.
Proof.
  all: unfold Bind.compM; intros; try ext x.
    rewrite Bind.assoc. reflexivity.
    apply Bind.bind_ret_l.
    apply Bind.bind_ret_r.
Defined.

Instance BindToJoin (M : Type -> Type) (inst : Bind.Monad M)
  : Join.Monad M :=
{
    is_applicative := @Bind.is_applicative M inst;
    join := @Bind.join M inst
}.
Proof.
  all: intros; unfold Bind.join, compose; try ext x.
    rewrite Bind.assoc, Bind.bind_fmap. unfold compose, id. reflexivity.
    rewrite Bind.bind_ret_l. reflexivity.
    rewrite Bind.bind_fmap, <- Bind.bind_ret_r. f_equal.
    rewrite Bind.bind_fmap, Bind.fmap_bind. f_equal.
    rewrite !Bind.bind_ap. Bind.monad.
Defined.

Section Axioms.

Variable M : Type -> Type.
Variable inst : Comp.Monad M.

Axiom compM_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> M C),
    Comp.compM (f .> ret) g = f .> g.

Axiom compM_comp' :
  forall (A B C : Type) (f : A -> B) (g : B -> M C) (x : A),
    Comp.compM (f .> ret) g x = g (f x).

Axiom compM_fmap :
  forall (A B C : Type) (f : A -> M B) (g : B -> C),
    Comp.compM f (g .> ret) = f .> fmap g.

(* old *)
Axiom comp_id :
  forall (A B : Type) (f : A -> M B) (x : A),
    Comp.compM id f (ret x) = f x.

Axiom comp_const :
  forall (A B C : Type) (f : B -> M C) (x : A) (mb : M B),
    Comp.compM (fun _ => mb) f x = Comp.bind mb f.

End Axioms.

Instance CompToBind (M : Type -> Type) (inst : Comp.Monad M)
  : Bind.Monad M :=
{
    is_applicative := @Comp.is_applicative M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
      @Comp.compM M inst unit A B (fun _ => ma) f tt
}.
Proof.
  all: intros.
    apply compM_comp'.
    rewrite Comp.compM_ret_r. reflexivity.
    Focus 2. rewrite ?comp_const.
Abort. (* TODO *)