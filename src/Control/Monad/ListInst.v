From CoqMTL Require Import Control.All.
From CoqMTL Require Import Control.Monad.Class.All.

From CoqMTL Require Import Misc.Monoid.

(** A monad that models nondeterministic computations. *)
Definition List (A : Type) : Type := list A.

(** [fmap] is taken directly from the standard library. *)
Definition fmap_List := map.

#[global] Hint Rewrite app_nil_l app_nil_r : CoqMTL.

#[refine]
#[export]
Instance Functor_List : Functor list :=
{
  fmap := fmap_List;
}.
Proof.
  all: cbn; unfold fmap_List, id, compose; intros; ext l.
  - now apply map_id.
  - now rewrite <- map_map.
Defined.

(**
  We can inject a value into the monad, because determinism is a
  degenerate case of nondeterminism.
*)
Definition pure_List {A : Type} (x : A) : list A := [x].

#[global] Hint Unfold List pure_List : CoqMTL.

(**
  Even though the definition of [ap] is straightforward, proving that
  it satisfies the [Applicative] laws is quite difficult, probably the
  most difficult of all [Applicative]s from this library.
*)
Fixpoint ap_list {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
match lf with
| []      => []
| f :: fs => map f la ++ ap_list fs la
end.

Lemma ap_list_nil_l :
  forall (A B : Type) (la : list A),
    @ap_list A B [] la = [].
Proof.
  now cbn.
Qed.

Lemma ap_list_nil_r :
  forall (A B : Type) (lf : list (A -> B)),
    ap_list lf [] = [].
Proof.
  now induction lf as [| f fs]; cbn.
Qed.

Lemma ap_list_app :
  forall (A B : Type) (lf lf' : list (A -> B)) (la : list A),
      ap_list (lf ++ lf') la = ap_list lf la ++ ap_list lf' la.
Proof.
  induction lf as [| f fs]; intros; cbn; [easy |].
  now rewrite <- app_assoc, IHfs.
Qed.

Lemma ap_list_map :
  forall (A B : Type) (f : A -> B) (la : list A),
    ap_list [f] la = map f la.
Proof.
  now induction la as [| x xs]; cbn in *; rewrite ?IHxs.
Qed.

Lemma ap_list_exchange2 :
  forall (A B C : Type) (g : B -> C) (fs : list (A -> B)) (xs : list A),
      ap_list (map (compose g) fs) xs = map g (ap_list fs xs).
Proof.
  induction fs as [| f fs]; cbn; intros; [easy |].
  now rewrite map_app, map_map, IHfs.
Qed.

#[refine]
#[export]
Instance Applicative_List : Applicative list :=
{
  is_functor := Functor_List;
  pure := @pure_List;
  ap := @ap_list;
}.
Proof.
  - cbn; intros.
    now rewrite map_id, app_nil_r.
  - induction g as [| g gs]; cbn; intros; [easy |].
    now rewrite ap_list_app, IHgs, ap_list_exchange2.
  - easy.
  - now induction f as [| f fs]; cbn in *; intros; rewrite ?IHfs.
  - now hs.
Defined.

Definition aempty_List {A : Type} : list A := [].

Definition aplus_List {A : Type} (x y : list A) : list A := app x y.

#[refine]
#[export]
Instance Alternative_List : Alternative list :=
{
  is_applicative := Applicative_List;
  aempty := @aempty_List;
  aplus := @aplus_List;
}.
Proof.
  - now apply app_nil_l.
  - now apply app_nil_r.
  - now apply app_assoc.
Defined.

(**
  We can sequence nondeterministic computations by feeding all possible
  arguments to [f] and then flattening the resulting list.
*)
Fixpoint bind_List {A B : Type} (la : list A) (f : A -> list B) : list B :=
match la with
| []     => []
| h :: t => f h ++ bind_List t f
end.

Lemma bind_List_app :
  forall (A B : Type) (l1 l2 : list A) (f : A -> list B),
    bind_List (l1 ++ l2) f = bind_List l1 f ++ bind_List l2 f.
Proof.
  induction l1 as [| h1 t1]; cbn; intros; [easy |].
  now rewrite IHt1, app_assoc.
Qed.

(** [list]'s nondeterminism is not commutative, because [app] isn't. *)
Lemma List_not_CommutativeApplicative :
  ~ CommutativeApplicative list Applicative_List.
Proof.
  destruct 1.
  specialize (ap_comm _ _ _ (fun _ => id) [true; false] [false; true]); compute in ap_comm.
  now inversion ap_comm.
Qed.

#[refine]
#[export]
Instance Monad_List : Monad list :=
{
  is_applicative := Applicative_List;
  bind := @bind_List;
}.
Proof.
  - now hs.
  - now induction ma as [| h t]; cbn in *; rewrite ?IHt.
  - induction ma as [| h t]; cbn; intros; [easy |].
    now rewrite bind_List_app, <- IHt.
  - induction mf as [| hf tf]; cbn; intros; [easy |].
    rewrite <- IHtf; f_equal.
    induction mx as [| h t]; cbn; [easy |].
    now rewrite IHt.
Defined.

(**
  [list] is the primordial example of a nondeterminism monad. A
  computation can fail by returning an empty list and nondeterministic
  choice is modeled by [app].
*)

#[refine]
#[export]
Instance MonadFail_List : MonadFail list Monad_List :=
{
  fail := fun A => [];
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance MonadAlt_List : MonadAlt list Monad_List :=
{
  choose := @app;
}.
Proof.
  - now intros; rewrite app_assoc.
  - induction x as [| h t]; cbn in *; intros; [easy |].
    now rewrite IHt, app_assoc.
Defined.

#[refine]
#[export]
Instance MonadNondet_List : MonadNondet list Monad_List :=
{
  instF := MonadFail_List;
  instA := MonadAlt_List;
}.
Proof.
  all: now hs.
Defined.

Fixpoint foldMap_List {A : Type} {M : Monoid} (f : A -> M) (l : list A) : M :=
match l with
| []     => neutr
| h :: t => op (f h) (foldMap_List f t)
end.

#[refine]
#[export]
Instance FoldableList : Foldable list :=
{
  foldMap := @foldMap_List;
}.
Proof.
  intros.
  ext l.
  induction l as [| h t]; unfold compose in *; cbn; [easy |].
  now rewrite IHt.
Defined.
