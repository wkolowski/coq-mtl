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
  all: intros; repeat
  match goal with
      | x : option _ |- _ => destruct x
  end; cbn; reflexivity.
Defined.

Instance MonadList : Monad list :=
{
    is_applicative := ApplicativeList;
    join := @join_List
}.
Proof.
  induction x as [| h t];
  unfold compose in *; simpl in *.
    trivial.
    rewrite IHt. induction h; simpl.
      trivial.
      rewrite <- app_assoc. rewrite IHh. trivial.
  cbn. apply app_nil_r.
  induction x as [| h t]; cbn in *; rewrite ?IHt; reflexivity.
  induction x as [| h t]; cbn in *.
    reflexivity.
    unfold fmap_List in *. rewrite map_app, IHt. reflexivity.
  induction mf as [| hf tf]; cbn in *; intros.
    reflexivity.
    rewrite IHtf. unfold compose. f_equal. induction ma as [| ha ta]; cbn.
      reflexivity.
      rewrite IHta. reflexivity.
Defined.

Instance MonadSum (A : Type) : Monad (sum A) :=
{
    is_applicative := ApplicativeSum A;
    join := @join_Sum A
}.
Proof.
  all: intros; repeat
  match goal with
      | x : _ + _ |- _ => destruct x
  end; reflexivity.
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
Proof. all: solveWriter. Defined.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    join := @join_State S
}.
Proof.
  all: cbn; unfold join_State, fmap_State, ret_State, ap_State, compose;
  intros; ext s; try destruct (x s); try reflexivity.
    destruct (mf s), (ma s0). reflexivity.
Defined.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    join := @join_Cont R
}.
Proof. all: reflexivity. Defined.