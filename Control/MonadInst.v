Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Control.Monad.

Require Import HSLib.Instances.All.

Require Import HSLib.MonadClass.MonadState.

Instance MonadIdentity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    bind := @bind_Identity
}.
Proof. all: reflexivity. Defined.

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
  induction x as [| h t]; cbn; intros.
    reflexivity.
    unfold compose in *. rewrite IHt. reflexivity.
  induction mf as [| hf tf]; cbn; intros.
    reflexivity.
    rewrite <- IHtf. f_equal. induction mx as [| h t]; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Defined.

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
  end; reflexivity.
Defined.

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
Proof. all: reflexivity. Defined.

Require Import Arith.

(* TODO: callCC wut? *)
Definition wut {R : Type} (b : bool) : Cont R nat :=
  do
    callCC (fun k =>
      when (b) (k 42);;
      ret 123).

Compute @wut False false.