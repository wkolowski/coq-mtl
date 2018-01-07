Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadBind.MonadInst.
Require Import HSLib.MonadComp.Monad.
Require Import HSLib.Instances.All.

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
  reflexivity.
Defined.

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
  trivial.
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
  trivial.
Defined.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    compM := @compM_Reader R
}.
Proof. all: trivial. Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    ret := @ret_Writer W;
    compM := @compM_Writer W
}.
Proof. all: solveWriter. Defined.

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
  trivial.
Defined.