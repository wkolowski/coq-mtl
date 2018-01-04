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

Axiom fmap_ret :
  forall (M : Type -> Type) (inst : Join.Monad M) (A B : Type) (f : A -> B)
    (x : A), fmap f (Join.ret x) = Join.ret (f x).

Axiom join_ret :
  forall (M : Type -> Type) (inst : Join.Monad M) (X : Type) (mx : M X),
    Join.join (Join.ret mx) = mx.

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
    unfold compose. rewrite fmap_ret, join_ret. reflexivity.
    rewrite <- Join.ret_law. unfold compose. rewrite join_ret. reflexivity.
    Focus 2. rewrite fmap_ret. reflexivity.
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
    apply Bind.id_left.
    apply Bind.id_right.
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
  intros. unfold compose. ext x. rewrite Bind.assoc, Bind.bind_fmap.
    unfold compose, id. reflexivity.
  intros. unfold compose. ext x. rewrite Bind.id_left, Bind.bind_fmap.
    unfold compose, id. rewrite Bind.id_right. reflexivity.
  intros. unfold compose, id. ext x. rewrite Bind.id_left. reflexivity.
  intros. rewrite Bind.fmap_ret. reflexivity.
Defined.

Instance CompToBind (M : Type -> Type) (inst : Comp.Monad M)
  : Bind.Monad M :=
{
    is_functor := @Comp.is_functor M inst;
    ret := @Comp.ret M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
      Comp.compM id f ma
}.
Proof.
  all: intros.
    Focus 2. rewrite Comp.id_right. reflexivity.
    Focus 3. rewrite Comp.fmap_ret. reflexivity.
    Focus 3. unfold compose, id. 
Abort.