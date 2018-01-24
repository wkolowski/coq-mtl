Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import HSLib.MonadComp.Monad.

Require Import HSLib.Instances.All.

Instance MonadIdentity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    compM := @compM_Identity
}.
Proof. all: reflexivity. Defined.

Instance MonadOption : Monad option :=
{
    is_applicative := ApplicativeOption;
    compM := @compM_Option
}.
Proof.
  intros. extensionality x. unfold compM_Option.
    destruct (f x); trivial.
  trivial.
  intros. extensionality x. unfold compM_Option.
    destruct (f x); trivial.
Defined.

Instance MonadList : Monad list :=
{
    is_applicative := ApplicativeList;
    compM := @compM_List
}.
Proof.
  intros. extensionality x. unfold compM_List. induction (f x); simpl.
    trivial.
    rewrite IHl. rewrite bind_List_app. trivial.
  intros. extensionality x. unfold ret_List, compM_List. simpl.
    apply app_nil_r.
  intros. extensionality x. unfold ret_List, compM_List.
    induction (f x); cbn in *; rewrite ?IHl; trivial.
Defined.

Instance MonadSum (E : Type) : Monad (sum E) :=
{
    is_applicative := ApplicativeSum E;
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
    is_applicative := ApplicativeReader R;
    compM := @compM_Reader R
}.
Proof. all: reflexivity. Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := ApplicativeWriter W;
    compM := @compM_Writer W
}.
Proof. all: solveWriter. Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    compM := @compM_State S
}.
Proof.
  intros. extensionality x. extensionality s. unfold compM_State.
    destruct (f x s). trivial.
  trivial.
  intros. extensionality x. extensionality s. unfold compM_State.
    destruct (f x s). trivial.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    compM := @compM_Cont R
}.
Proof. all: reflexivity. Defined.