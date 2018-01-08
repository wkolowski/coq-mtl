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
    is_applicative := ApplicativeOption;
    bind := @bind_Option
}.
Proof.
  all: intros; try
  match goal with
      | x : option _ |- _ => destruct x
  end; cbn in *; reflexivity.
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
    is_applicative := ApplicativeList;
    bind := @bind_List
}.
Proof.
  all: cbn.
  intros. rewrite app_nil_r. reflexivity.
  induction ma as [| h t]; cbn; rewrite ?IHt; reflexivity.
  induction ma as [| h t]; cbn; intros.
    trivial.
    rewrite bind_List_app, <- IHt. trivial.
  trivial.
  induction x as [| h t]; cbn; intros.
    reflexivity.
    unfold compose in *. rewrite IHt. reflexivity.
  induction x as [| h t]; cbn; intros.
    reflexivity.
    unfold fmap_List. rewrite map_app, IHt. reflexivity.
  induction mf as [| hf tf]; cbn; intros.
    reflexivity.
    rewrite <- IHtf. f_equal. induction mx as [| h t]; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
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

Compute init [1; 2; 3].
Compute filterM (fun _ => [true; false]) [1; 2; 3].
Compute replicateM 3 [1; 2].
Compute sequence [[1]; [2]].

Instance MonadSum (A : Type) : Monad (sum A) :=
{
    is_applicative := ApplicativeSum A;
    bind := @bind_Sum A
}.
Proof.
  all: intros; try
  match goal with
      | x : _ + _ |- _ => destruct x
  end; cbn in *; reflexivity.
Defined.

Eval cbn in sequence [inr 42; inr 5; inr 10].
Eval cbn in sequence [inr 42; inr 5; inr 10; inl (fun n : nat => 2 * n)].

Eval simpl in foldM (fun n m => inl (plus n m)) 0 [1; 2; 3].

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_applicative := ApplicativeReader R;
    bind := @bind_Reader R
}.
Proof. all: reflexivity. Defined.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := ApplicativeWriter W;
    bind := @bind_Writer W
}.
Proof. all: solveWriter. Defined.

Instance Monad_State (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    bind := @bind_State S
}.
Proof.
  all: compute; intros; ext s;
  try match goal with
      | x : ?S -> _ * ?S, s : ?S |- _ => destruct (x s)
  end; trivial.
Defined.

Require Import HSLib.MonadBind.MonadState.

Instance MonadState_State
  (S : Type) : MonadState S (State S) (Monad_State S) :=
{
    get := fun s : S => (s, s);
    put := fun s : S => fun _ => (tt, s)
}.
Proof. all: reflexivity. Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    bind := @bind_Cont R
}.
Proof. all: trivial. Defined.