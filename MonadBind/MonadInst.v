Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import Logic.FunctionalExtensionality.

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.

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
    ret := @Some;
    bind := @bind_Option
}.
Proof.
  simpl. trivial.
  destruct ma; simpl; trivial.
  intros. destruct ma; simpl.
    destruct (f a); simpl; trivial.
    trivial.
  trivial.
  destruct x; cbn; reflexivity.
Defined.

Eval compute in (fun _ => Some 5) >=> (fun n => Some (n + 6)).
Eval compute in Some 4 >>= fun n : nat => Some (2 * n).

Eval compute in liftM2 plus (Some 2) (Some 4).
Eval compute in liftM2 plus (Some 42) None.

Lemma bind_List_app : forall (A B : Type) (l1 l2 : list A) (f : A -> list B),
    bind_List (l1 ++ l2) f = bind_List l1 f ++ bind_List l2 f.
Proof.
  induction l1 as [| h1 t1]; simpl.
    trivial.
    intros. rewrite IHt1. rewrite app_assoc. trivial.
Qed.

Instance MonadList : Monad list :=
{
    is_functor := FunctorList;
    ret := fun (A : Type) (a : A) => [a];
    bind := @bind_List
}.
Proof.
  intros. simpl. rewrite app_nil_r. trivial.
  intros. induction ma as [| h t]; simpl; try rewrite IHt; trivial.
  induction ma as [| h t]; simpl.
    trivial.
    intros. rewrite bind_List_app. rewrite <- IHt. trivial.
  trivial.
  induction x as [| h t]; cbn; intros.
    reflexivity.
    unfold compose in *. rewrite IHt. reflexivity.
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
    bind := @bind_Sum A
}.
Proof.
  intros. simpl. trivial.
  intros. unfold ret_Sum. destruct ma; simpl; trivial.
  intros. destruct ma; simpl.
    trivial.
    destruct (f a); simpl; trivial.
  trivial.
  destruct x; cbn; unfold compose; reflexivity.
Defined.

Eval simpl in sequence [inr 42; inr 5; inr 10].
Eval simpl in sequence [inr 42; inr 5; inr 10; inl (fun n : nat => 2 * n)].

Eval simpl in foldM (fun n m => inl (plus n m)) 0 [1; 2; 3].

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    bind := @bind_Reader R
}.
Proof. all: trivial. Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_functor := FunctorWriter W;
    ret := @ret_Writer W;
    bind := @bind_Writer W
}.
Proof. all: solveWriter. Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    bind := @bind_State S
}.
Proof.
  trivial.
  unfold ret_State, bind_State. intros. extensionality s.
    destruct (ma s). trivial.
  unfold ret_State, bind_State. intros. extensionality s.
    destruct (ma s). trivial.
  trivial.
  cbn; intros. ext s. compute. destruct (x s). reflexivity.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_functor := FunctorCont R;
    ret := @ret_Cont R;
    bind := @bind_Cont R
}.
Proof. all: trivial. Defined.