Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Instances.All.

Require Import HSLib.Functor.Functor.
Require Import HSLib.MonadJoin.Monad.
Require Import HSLib.MonadJoin.MonadInst.
(*
Class FreeMonad (M : Type -> Type) : Type :=
{
    is_monad : Monad M;
    F : Type -> Type;
    is_functor : Functor F;
    wrap : forall {A : Type}, F (M A) -> M A;
    dupa : forall (A B : Type) (f : A -> M B) (x : F A),
        wrap (fmap f x) = wrap (fmap ret x) >>= f
}.

Definition ret_Identity {A : Type} (x : A) : Identity A := x.

Definition join_Identity {A : Type} (x : Identity (Identity A)) : Identity A := x.

Instance FreeMonad2_Identity : FreeMonad Identity :=
{
    is_monad := MonadIdentity;
    F := Identity;
    is_functor := FunctorIdentity;
    wrap := @join_Identity
}.
Proof. auto. Defined.

Inductive RoseTree (A : Type) : Type :=
    | Leaf : A -> RoseTree A
    | Node : list (RoseTree A) -> RoseTree A.

Arguments Leaf [A] _.
Arguments Node [A] _.

Require Import List.
Import ListNotations.

Fixpoint fmap_RoseTree {A B : Type} (f : A -> B) (t : RoseTree A)
    : RoseTree B :=
match t with
    | Leaf x => Leaf (f x)
    | Node [] => Node []
    | Node (h :: t) => Node (fmap_RoseTree f h :: map (fmap_RoseTree f) t)
end.

Require Import FunctionalExtensionality.

Instance FunctorRT : Functor RoseTree :=
{
    fmap := @fmap_RoseTree
}.
Proof.
  intros. extensionality t. destruct t.
    simpl. trivial.
    simpl. destruct l.
      trivial.
Abort.
*)