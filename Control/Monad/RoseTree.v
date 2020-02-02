Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** Rose Trees are trees which hold values only in their leaves. This
    type has a monad structure, but I don't know what kind of effect
    it models. As we will see below, it is not nondeterminism. *)
Inductive RT (A : Type) : Type :=
    | Leaf : A -> RT A
    | Node : RT A -> RT A -> RT A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

(** We can map over such computations in the obvious way, by applying the
    function to each leaf. *)
Fixpoint fmap_RT {A B : Type} (f : A -> B) (t : RT A) : RT B :=
match t with
    | Leaf x => Leaf (f x)
    | Node l r => Node (fmap_RT f l) (fmap_RT f r)
end.

#[refine]
Instance Functor_RT : Functor RT :=
{
    fmap := @fmap_RT
}.
Proof.
  all: intros; ext t;
  induction t as [x | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
Defined.

(** We can inject a value into the monad by putting it into a [Leaf]. *)
Definition pure_RT {A : Type} (x : A) : RT A := Leaf x.

(** Applying a tree of functions to a tree of arguments is also quite
    easy: there's one function in each [Leaf] and we can replace it by
    the result of mapping it over the tree of arguments. *)
Fixpoint ap_RT {A B : Type} (tf : RT (A -> B)) (ta : RT A) : RT B :=
match tf with
    | Leaf f => fmap f ta
    | Node l r => Node (ap_RT l ta) (ap_RT r ta)
end.

#[refine]
Instance Applicative_RT : Applicative RT :=
{
    pure := @pure_RT;
    ap := @ap_RT;
}.
Proof.
  all: cbn; intros.
    cbn. rewrite (@fmap_id _ Functor_RT). reflexivity.
    induction g as [g | gl IHgl gr IHgr]; cbn.
      induction f as [f | fl IHfl fr IHfr]; cbn.
        rewrite (@fmap_comp' _ Functor_RT). reflexivity.
        rewrite IHfl, IHfr. reflexivity.
      rewrite IHgl, IHgr. reflexivity.
    reflexivity.
    induction f as [f | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
    reflexivity.
Defined.

(** Constructors are injective, so [RoseTree] can't be a commutative
    applicative functor. *)
Lemma RT_not_CommutativeApplicative :
  ~ CommutativeApplicative _ Applicative_RT.
Proof.
  destruct 1.
  specialize (ap_comm bool bool _ (fun _ => id)
    (Node (Leaf false) (Leaf true)) (Node (Leaf true) (Leaf false))).
  compute in *. congruence.
Qed.

(** [RoseTree]s are nonempty, so we can't make a tree full of [False]s
    out of nowhere. *)
Lemma RT_not_Alternative :
  Alternative RT -> False.
Proof.
  destruct 1. induction (aempty False); contradiction.
Qed.

(** We can sequence two trees by replacing each leaf in the tree [ta]
    by the reuslt of applying [tf] to the value it contains. *)
Fixpoint bind_RT {A B : Type} (ta : RT A) (tf : A -> RT B) : RT B :=
match ta with
    | Leaf x => tf x
    | Node l r => Node (bind_RT l tf) (bind_RT r tf)
end.

#[refine]
Instance Monad_RT : Monad RT :=
{
    bind := @bind_RT
}.
Proof.
  all: cbn; intros.
    reflexivity.
    induction ma as [a | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
    induction ma as [a | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
    induction mf as [f | fl IHfl fr IHfr]; cbn.
      induction mx as [x | xl IHxl xr IHxr]; cbn.
        reflexivity.
        rewrite IHxl, IHxr. reflexivity.
      rewrite IHfl, IHfr. reflexivity.
Defined.

(** Rose trees can't have a [fail] function, because they are nonempty
    and thus we can't produce a tree of [False]s out of nowhere. *)
Lemma RT_not_MonadFail :
  MonadFail RT Monad_RT -> False.
Proof.
  destruct 1. induction (fail False); assumption.
Qed.

(** Therefore they also can't model nondeterministic computations. *)
Lemma RT_not_MonadNondet :
  MonadNondet RT Monad_RT -> False.
Proof.
  destruct 1. apply RT_not_MonadFail. assumption.
Qed.

(** TODO: the real question is however, whether [RT] can be made an
    instance of [MonadAlt]. *)

Fixpoint foldMap_RT
  {A : Type} {M : Monoid} (f : A -> M) (t : RT A) : M :=
match t with
    | Leaf x => f x
    | Node l r => op (foldMap_RT f l) (foldMap_RT f r)
end.

#[refine]
Instance Foldable_RT : Foldable RT :=
{
    foldMap := @foldMap_RT
}.
Proof.
  intros. ext t.
  induction t as [| l IHl r IHr]; unfold compose in *; cbn; congruence.
Defined.