Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Functor.Functor.
Require Import HSLib.MonadJoin.Monad.
Require Import HSLib.Instances.Id.

(*Class FreeMonad (T : (Type -> Type) -> (Type -> Type)) : Type :=
{
    cond : forall F : Type -> Type, Functor F -> Monad (T F);
    wrap : forall F : Type -> Type, Functor F ->
        forall X : Type, F (T F X) -> T F X
}.*)

Class FreeMonad2 (M : Type -> Type) : Type :=
{
    is_monad : Monad M;
    F : Type -> Type;
    is_functor : Functor F;
    wrap : forall {A : Type}, F (M A) -> M A;
    dupa : forall (A B : Type) (f : A -> M B) (x : F A),
        wrap (fmap f x) = wrap (fmap ret x) >>= f
}.

Definition ret_Id {A : Type} (x : A) : Id A := x.

Definition join_Id {A : Type} (x : Id (Id A)) : Id A := x.

Instance MonadId : Monad Id :=
{
    is_functor := FunctorId;
    ret := @ret_Id;
    join := @join_Id
}.
Proof. auto. auto. Defined.

Instance FreeMonad2_Identity : FreeMonad2 Id :=
{
    is_monad := MonadId;
    F := Id;
    is_functor := FunctorId;
    wrap := @join_Id
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