Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.Monad.

Require Import HSLib.Instances.All.

Instance MonadIdentity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    join := @join_Identity
}.
Proof. all: reflexivity. Defined.

Instance MonadOption : Monad option :=
{
    is_applicative := ApplicativeOption;
    join := @join_Option
}.
Proof.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt as [[[ssx |] |] |]; auto.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt; auto.
  destruct ma; reflexivity.
Defined.

Instance MonadList : Monad list :=
{
    is_applicative := ApplicativeList;
    join := @join_List
}.
Proof.
  intro. extensionality lla. induction lla as [| h t];
  unfold compose in *; simpl in *.
    trivial.
    rewrite IHt. induction h; simpl.
      trivial.
      rewrite <- app_assoc. rewrite IHh. trivial.
  intro. extensionality lla. induction lla as [| h t];
  unfold compose in *; simpl in *.
    trivial.
    f_equal. rewrite <- IHt. trivial.
  cbn. apply app_nil_r.
Defined.

Instance MonadSum (A : Type) : Monad (sum A) :=
{
    is_applicative := ApplicativeSum A;
    join := @join_Sum A
}.
Proof.
  intro B. extensionality x.
    destruct x as [a | [a | [a | b]]]; compute; trivial.
  intro B. extensionality x.
    destruct x as [a | b]; compute; trivial.
  destruct ma; reflexivity.
Defined.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_applicative := ApplicativeReader R;
    join := @join_Reader R
}.
Proof. all: reflexivity. Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := ApplicativeWriter W;
    join := @join_Writer W
}.
Proof.
  intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wwwx. destruct wwwx as [[[x w] w'] w''].
    rewrite op_assoc. trivial.
  intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wx. destruct wx as [x w]. rewrite id_left, id_right. auto.
  intros. cbn. destruct ma. rewrite id_right. reflexivity.
Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    join := @join_State S
}.
Proof.
  intros. extensionality s3x. extensionality s1.
    simpl. unfold join_State, fmap_State, compose. destruct (s3x s1).
    destruct (s s0). trivial.
  intros. extensionality sx. extensionality s.
    simpl. unfold ret_State, join_State, fmap_State, compose.
    destruct (sx s). trivial.
  reflexivity.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    join := @join_Cont R
}.
Proof. all: reflexivity. Defined.