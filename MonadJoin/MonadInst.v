Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadJoin.Monad.

Require Import HSLib.Instances.Option.
Require Import HSLib.Instances.ListInst.
Require Import HSLib.Instances.Sum.
Require Import HSLib.Instances.Reader.
Require Import HSLib.Instances.Writer.
Require Import HSLib.Instances.State.
Require Import HSLib.Instances.Cont.
Require Import HSLib.Instances.Identity.

Instance MonadOption : Monad option :=
{
    is_functor := FunctorOption;
    ret := Some;
    join := @join_Option
}.
Proof.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt as [[[ssx |] |] |]; auto.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt; auto.
Defined.

Eval compute in (fun _ => Some 5) >=> (fun n => Some (n + 6)).
Eval compute in Some 4 >>= fun n : nat => Some (2 * n).

Eval compute in liftM2 plus (Some 2) (Some 4).
Eval compute in liftM2 plus (Some 42) None.

(** * List *)

Instance MonadList : Monad list :=
{
    ret := fun (A : Type) (a : A) => [a];
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
Defined.

Definition head {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | [_] => Some []
    | h :: t => liftM2 (@cons A) (ret h) (init t)
end.

Eval compute in init [1; 2; 3].

Eval simpl in filterM (fun _ => [true; false]) [1; 2; 3].

Eval simpl in replicateM 3 [1; 2].

Eval simpl in sequence [[1]; [2]].

Instance MonadSum (A : Type) : Monad (sum A) :=
{
    is_functor := FunctorSum A;
    ret := @ret_Sum A;
    join := @join_Sum A
}.
Proof.
  intro B. extensionality x.
    destruct x as [a | [a | [a | b]]]; compute; trivial.
  intro B. extensionality x.
    destruct x as [a | b]; compute; trivial.
Defined.

Eval simpl in sequence [inr 42; inr 5; inr 10].
Eval simpl in sequence [inr 42; inr 5; inr 10; inl (fun n : nat => 2 * n)].

Eval simpl in foldM (fun n m => inl (plus n m)) 0 [1; 2; 3].

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    join := @join_Reader R
}.
Proof.
  trivial.
  trivial.
Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    ret := @ret_Writer W;
    join := @join_Writer W
}.
Proof.
  * intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wwwx. destruct wwwx as [[[x w] w'] w''].
    rewrite op_assoc. trivial.
  * intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wx. destruct wx as [x w]. rewrite id_left, id_right. auto.
Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    join := @join_State S
}.
Proof.
  intros. extensionality s3x. extensionality s1.
    simpl. unfold join_State, fmap_State, compose. destruct (s3x s1).
    destruct (s s0). trivial.
  intros. extensionality sx. extensionality s.
    simpl. unfold ret_State, join_State, fmap_State, compose.
    destruct (sx s). trivial.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    ret := @ret_Cont R;
    join := @join_Cont R
}.
Proof.
  trivial.
  trivial.
Defined.

Definition ret_Identity {A : Type} (x : A) : Identity A := x.

Definition join_Identity {A : Type} (x : Identity (Identity A))
  : Identity A := x.

Instance MonadIdentity : Monad Identity :=
{
    is_functor := FunctorIdentity;
    ret := @ret_Identity;
    join := @join_Identity
}.
Proof. auto. auto. Defined.

