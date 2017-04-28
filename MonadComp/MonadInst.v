Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadComp.Monad.

Require Import HSLib.Instances.Option.
Require Import HSLib.Instances.ListInst.
Require Import HSLib.Instances.Sum.
Require Import HSLib.Instances.Reader.
Require Import HSLib.Instances.Writer.
Require Import HSLib.Instances.State.
Require Import HSLib.Instances.Cont.

Instance MonadOption : Monad option :=
{
    is_functor := FunctorOption;
    ret := @ret_Option;
    compM := @compM_Option
}.
Proof.
  intros. extensionality x. unfold compM_Option.
    destruct (f x); trivial.
  trivial.
  intros. extensionality x. unfold compM_Option.
    destruct (f x); trivial.
Defined.
(* end hide *)

(*Fixpoint joinL {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | h :: t => h ++ joinL t
end.

Definition compL {A B C : Type} (f : A -> list B) (g : B -> list C)
    (a : A) : list C := joinL (fmap g (f a)).*)

Instance MonadList : Monad list :=
{
    is_functor := FunctorList;
    ret := @ret_List;
    compM := @compM_List
}.
Proof.
  intros. extensionality x. unfold compM_List. induction (f x); simpl.
    trivial.
    rewrite IHl. rewrite bind_List_app. trivial.
  intros. extensionality x. unfold ret_List, compM_List. simpl.
    apply app_nil_r.
  intros. extensionality x. unfold ret_List, compM_List.
    induction (f x); simpl; try rewrite IHl; trivial.
Defined.

Instance MonadSum (E : Type) : Monad (sum E) :=
{
    is_functor := FunctorSum E;
    ret := @ret_Sum E;
    compM := @compM_Sum E
}.
Proof.
  intros. extensionality x. unfold compM_Sum.
    destruct (f x); simpl; trivial.
  trivial.
  intros. extensionality x. unfold compM_Sum.
    destruct (f x); simpl; trivial.
Defined.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    compM := @compM_Reader R
}.
Proof.
  trivial.
  trivial.
  trivial.
Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    ret := @ret_Writer W;
    compM := @compM_Writer W
}.
Proof.
  solveWriter.
  solveWriter.
  solveWriter.
Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    compM := @compM_State S
}.
Proof.
  intros. extensionality x. extensionality s. unfold compM_State.
    destruct (f x s). trivial.
  trivial.
  intros. extensionality x. extensionality s. unfold compM_State.
    destruct (f x s). trivial.
Defined.

