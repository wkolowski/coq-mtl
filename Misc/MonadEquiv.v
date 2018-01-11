Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Module Join.
Require Import HSLib.MonadJoin.Monad.
Include HSLib.MonadJoin.Monad.
End Join.

Module Bind.
Require Import HSLib.MonadBind.Monad.
Include HSLib.MonadBind.Monad.
End Bind.

Module Comp.
Require Import HSLib.MonadComp.Monad.
Include HSLib.MonadComp.Monad.
End Comp.

Require Import HSLib.Applicative.Applicative.

Instance JoinToBind (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_applicative := @Join.is_applicative M inst;
    bind := @Join.bind M inst
}.
Proof.
  apply Join.bind_ret_l.
  apply Join.bind_ret_r.
  apply Join.assoc.
  apply Join.bind_fmap.
  apply Join.fmap_bind.
  intros. admit.
Admitted.

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

Axiom comp_id :
  forall (M : Type -> Type) (inst : Comp.Monad M) (A B : Type) (f : A -> M B)
  (x : A),
    Comp.compM id f (ret x) = f x.

Axiom comp_const :
  forall (M : Type -> Type) (inst : Comp.Monad M) (A B C : Type)
  (f : B -> M C) (x : A) (mb : M B),
    Comp.compM (fun _ => mb) f x = Comp.bind mb f.

Instance CompToBind (M : Type -> Type) (inst : Comp.Monad M)
  : Bind.Monad M :=
{
    is_applicative := @Comp.is_applicative M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
      @Comp.compM M inst unit A B (fun _ => ma) f tt
}.
Proof.
  all: intros.
    Focus 2. rewrite Comp.id_right. reflexivity.
    Focus 2. rewrite comp_const.
Abort. (* TODO *)