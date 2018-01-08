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
(*
Axiom fmap_join :
  forall (M : Type -> Type) (inst : Join.Monad M) (A B : Type) (f : A -> B)
    (x : M (M A)),
      fmap f (Join.join x) = Join.join (fmap (fmap f) x).

Axiom fmap_pres_comp' :
  forall (M : Type -> Type) (inst : Join.Monad M) (A B C : Type)
  (f : A -> B) (g : B -> C) (x : M A),
    fmap (fun x : A => g (f x)) x = fmap g (fmap f x).

Instance JoinToBind (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_functor := @Join.is_functor M inst;
    ret := @Join.ret M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
        (fmap f .> Join.join) ma
}.
Proof.
  all: intros.
    unfold compose. rewrite Join.fmap_ret, Join.join_ret. reflexivity.
    rewrite <- Join.ret_law. unfold compose. rewrite Join.join_ret.
      reflexivity.
    Focus 2. rewrite Join.fmap_ret. reflexivity.
    Focus 2. unfold compose. rewrite <- fmap_pres_comp'. reflexivity.
    unfold compose. rewrite fmap_join, <- ?fmap_pres_comp'.
Abort.

Instance BindToComp (M : Type -> Type) (inst : Bind.Monad M)
  : Comp.Monad M :=
{
    is_functor := @Bind.is_functor M inst;
    ret := @Bind.ret M inst;
    compM := fun (A B C : Type) (f : A -> M B) (g : B -> M C) =>
        fun a : A => Bind.bind (f a) g
}.
Proof.
  all: intros; try ext x.
    rewrite Bind.assoc. reflexivity.
    apply Bind.bind_ret_l.
    apply Bind.bind_ret_r.
    apply Bind.fmap_ret.
Defined.

Instance BindToJoin (M : Type -> Type) (inst : Bind.Monad M)
  : Join.Monad M :=
{
    is_functor := @Bind.is_functor M inst;
    ret := @Bind.ret M inst;
    join := fun (A : Type) (x : M (M A)) =>
        Bind.bind x id
}.
Proof.
  all: intros; unfold compose; try ext x.
    rewrite Bind.assoc, Bind.bind_fmap. unfold compose, id. reflexivity.
    rewrite Bind.bind_ret_l, Bind.bind_fmap, id_right, Bind.bind_ret_r.
      reflexivity.
    rewrite Bind.bind_ret_l. reflexivity.
    rewrite Bind.fmap_ret. reflexivity.
  rewrite Bind.bind_ret_l. reflexivity.
Defined.

Axiom comp_id :
  forall (M : Type -> Type) (inst : Comp.Monad M) (A B : Type) (f : A -> M B)
  (x : A),
    Comp.compM id f (Comp.ret x) = f x.

Axiom comp_const :
  forall (M : Type -> Type) (inst : Comp.Monad M) (A B C : Type)
  (f : B -> M C) (x : A) (mb : M B),
    Comp.compM (fun _ => mb) f x = Comp.bind mb f.

Instance CompToBind (M : Type -> Type) (inst : Comp.Monad M)
  : Bind.Monad M :=
{
    is_functor := @Comp.is_functor M inst;
    ret := @Comp.ret M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
      @Comp.compM M inst unit A B (fun _ => ma) f tt
}.
Proof.
  all: intros.
    Focus 2. rewrite Comp.id_right. reflexivity.
    Focus 3. rewrite Comp.fmap_ret. reflexivity.
    Focus 2. rewrite comp_const.
Abort.
*)