Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import HSLib.MonadJoin.Monad.

Require Import HSLib.Instances.All.

Definition join_Identity
  {A : Type} (x : Identity (Identity A)) : Identity A := x.

Instance MonadIdentity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    join := @join_Identity
}.
Proof. all: hs. Defined.

Definition join_Option
  {A : Type} (ooa : option (option A)) : option A :=
match ooa with
    | Some (Some x) => Some x
    | _ => None
end.

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

Fixpoint join_List {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | hl :: tll => hl ++ join_List tll
end.

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

Definition join_Sum {E A : Type} (ssa : sum E (sum E A)) : sum E A :=
match ssa with
    | inl e => inl e
    | inr sa =>
        match sa with
            | inl e => inl e
            | inr a => inr a
        end
end.

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

Definition join_Reader
  {R A : Type} (rra : Reader R (Reader R A)) : Reader R A :=
    fun r : R => rra r r.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    is_applicative := ApplicativeReader R;
    join := @join_Reader R
}.
Proof. all: reflexivity. Defined.

Definition join_Writer
  {W : Monoid} {A : Type} (wwa : Writer W (Writer W A)) : Writer W A :=
    let '((a, w'), w) := wwa in (a, op w w').

Hint Unfold join_Writer : HSLib.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    is_applicative := ApplicativeWriter W;
    join := @join_Writer W
}.
Proof. all: hs; repeat unmatch_all; hs. Defined.

Definition join_State
  {S A : Type} (ssa : State S (State S A)) : State S A :=
    fun s : S => let (f, s') := ssa s in f s'.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    join := @join_State S
}.
Proof.
  all: cbn; unfold join_State, fmap_State, pure_State, ap_State, compose;
  intros; ext s; try destruct (x s); try reflexivity.
    destruct (mf s), (ma s0). reflexivity.
Defined.

Definition join_Cont
  {R A : Type} (cca : Cont R (Cont R A)) : Cont R A :=
    fun f : A -> R => cca (fun g : (A -> R) -> R => g f).

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    join := @join_Cont R
}.
Proof. all: reflexivity. Defined.