Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** A monad that models nondeterministic computations. *)
Definition List (A : Type) : Type := list A.

(** [fmap] is taken directly from the standard library. *)
Definition fmap_List := map.

Hint Rewrite app_nil_l app_nil_r : CoqMTL.

Instance Functor_List : Functor list :=
{
    fmap := fmap_List
}.
Proof.
  all: cbn; unfold fmap_List, id, compose; intros; ext l.
    apply map_id.
    rewrite <- map_map. reflexivity.
Defined.

(** We can inject a value into the monad, because determinism is a
    degenerate case of nondeterminism. *)
Definition pure_List {A : Type} (x : A) : list A := [x].

Hint Unfold List pure_List : CoqMTL.

(** Even though the definition of [ap] is straightforward, proving that
    it satisfies the [Applicative] laws is quite difficult, probably the
    most difficult of all [Applicative]s from this library. *)
Fixpoint ap_list {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
match lf with
    | [] => []
    | f :: fs => map f la ++ ap_list fs la
end.

Lemma ap_list_nil_l :
  forall (A B : Type) (la : list A),
    @ap_list A B [] la = [].
Proof. cbn. reflexivity. Qed.

Lemma ap_list_nil_r :
  forall (A B : Type) (lf : list (A -> B)),
    ap_list lf [] = [].
Proof.
  induction lf as [| f fs]; auto.
Qed.

Lemma ap_list_app :
  forall (A B : Type) (lf lf' : list (A -> B)) (la : list A),
      ap_list (lf ++ lf') la = ap_list lf la ++ ap_list lf' la.
Proof.
  induction lf as [| f fs]; intros; cbn.
    reflexivity.
    rewrite <- app_assoc. rewrite IHfs. reflexivity.
Qed.

Lemma ap_list_map :
  forall (A B : Type) (f : A -> B) (la : list A),
    ap_list [f] la = map f la.
Proof.
  induction la as [| x xs]; cbn in *; rewrite ?IHxs; reflexivity.
Qed.

Lemma ap_list_exchange :
  forall (A B : Type) (x : A) (lf : list (A -> B)),
    ap_list [fun f : A -> B => f x] lf = ap_list lf [x].
Proof.
  induction lf as [| f fs]; cbn in *; rewrite ?IHfs; reflexivity.
Qed.

Lemma ap_list_exchange2 :
  forall (A B C : Type) (g : B -> C) (fs : list (A -> B)) (xs : list A),
      ap_list (map (compose g) fs) xs = map g (ap_list fs xs).
Proof.
  induction fs as [| f fs]; cbn; intros.
    reflexivity.
    rewrite map_app, map_map. f_equal. apply IHfs.
Qed.

Lemma ap_list_exchange3 :
  forall
    (A B C : Type) (f : A -> B) (fs : list (A -> B)) (gs : list (B -> C))
    (xs : list A),
      ap_list (ap_list (map compose gs) (f :: fs)) xs =
      ap_list gs (map f xs ++ ap_list fs xs).
Proof.
  induction gs as [| g gs]; cbn; intros.
    reflexivity.
    rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app, ap_list_exchange2. f_equal.
        apply IHgs.
Qed.

Instance Applicative_List : Applicative list :=
{
    is_functor := Functor_List;
    pure := @pure_List; 
    ap := @ap_list
}.
Proof.
  3, 5: hs.
  induction ax; cbn in *; rewrite ?IHax; reflexivity.
  induction f as [| f fs]; induction g as [| g gs]; cbn; intros.
    reflexivity.
    rewrite ?ap_list_nil_r. cbn. reflexivity.
    reflexivity.
    rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app. f_equal.
        apply ap_list_exchange2.
        rewrite app_nil_r. apply ap_list_exchange3.
  induction f as [| f fs]; cbn in *; intros; rewrite ?IHfs; reflexivity.
Defined.

Definition aempty_List {A : Type} : list A := [].

Definition aplus_List {A : Type} (x y : list A) : list A := app x y.

Instance Alternative_List : Alternative list :=
{
    is_applicative := Applicative_List;
    aempty := @aempty_List;
    aplus := @aplus_List
}.
Proof.
  apply app_nil_l.
  apply app_nil_r.
  apply app_assoc.
Defined.

(** We can sequence nondeterministic computations by feeding all possible
    arguments to [f] and then flattening the resulting list. *)
Fixpoint bind_List {A B : Type} (la : list A) (f : A -> list B) : list B :=
match la with
    | [] => []
    | h :: t => f h ++ bind_List t f
end.

Lemma bind_List_app :
  forall (A B : Type) (l1 l2 : list A) (f : A -> list B),
    bind_List (l1 ++ l2) f = bind_List l1 f ++ bind_List l2 f.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, app_assoc. reflexivity.
Qed.

(** [list]'s nondeterminism is not commutative, because [app] isn't. *)
Lemma List_not_CommutativeApplicative :
  ~ CommutativeApplicative list Applicative_List.
Proof.
  destruct 1.
  specialize (ap_comm _ _ _ (fun _ => id) [true; false] [false; true]).
  compute in ap_comm. inversion ap_comm.
Qed.

Instance Monad_List : Monad list :=
{
    is_applicative := Applicative_List;
    bind := @bind_List
}.
Proof.
  hs.
  induction ma as [| h t]; cbn in *; rewrite ?IHt; reflexivity.
  induction ma as [| h t]; cbn; intros.
    reflexivity.
    rewrite bind_List_app, <- IHt. reflexivity.
  induction mf as [| hf tf]; cbn; intros.
    reflexivity.
    rewrite <- IHtf. f_equal. induction mx as [| h t]; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Defined.

(** [list] is the primordial example of a nondeterminism monad. A
    computation can fail by returning an empty list and nondeterministic
    choice is modeled by [app]. *)

Instance MonadFail_List : MonadFail list Monad_List :=
{
    fail := fun A => []
}.
Proof. intros. cbn. reflexivity. Defined.

Instance MonadAlt_List : MonadAlt list Monad_List :=
{
    choose := @app;
}.
Proof.
  intros. rewrite app_assoc. reflexivity.
  induction x as [| h t]; cbn in *; intros.
    reflexivity.
    rewrite IHt, app_assoc. reflexivity.
Defined.

Instance MonadNondet_List : MonadNondet list Monad_List :=
{
    instF := MonadFail_List;
    instA := MonadAlt_List;
}.
Proof. all: hs. Defined.

Fixpoint foldMap_List
  {A : Type} {M : Monoid} (f : A -> M) (l : list A) : M :=
match l with
    | [] => neutr
    | h :: t => op (f h) (foldMap_List f t)
end.

Instance FoldableList : Foldable list :=
{
    foldMap := @foldMap_List
}.
Proof.
  intros. ext l.
  induction l as [| h t]; unfold compose in *; cbn; congruence.
Defined.