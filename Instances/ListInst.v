Require Import Control.

Definition List (A : Type) : Type := list A.

Definition fmap_List := map.

Hint Rewrite app_nil_l app_nil_r : HSLib.

Instance FunctorList : Functor list :=
{
    fmap := fmap_List
}.
Proof.
  all: cbn; unfold fmap_List, id, compose; intros; ext l.
    apply map_id.
    rewrite <- map_map. reflexivity.
Defined.

Definition pure_List {A : Type} (x : A) : list A := [x].

Hint Unfold List pure_List : HSLib.

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
  induction lf as [| f fs]; intros; simpl.
    trivial.
    rewrite <- app_assoc. rewrite IHfs. trivial.
Qed.

Lemma ap_list_map :
  forall (A B : Type) (f : A -> B) (la : list A),
    ap_list [f] la = map f la.
Proof.
  induction la as [| x xs]; simpl in *.
    trivial.
    rewrite IHxs. trivial.
Qed.

Lemma ap_list_exchange :
  forall (A B : Type) (x : A) (lf : list (A -> B)),
    ap_list [fun f : A -> B => f x] lf = ap_list lf [x].
Proof.
  induction lf as [| f fs]; simpl in *.
    trivial.
    rewrite IHfs. trivial.
Qed.

Lemma ap_list_exchange2 :
  forall (A B C : Type) (g : B -> C) (fs : list (A -> B)) (xs : list A),
      ap_list (map (compose g) fs) xs = map g (ap_list fs xs).
Proof.
  induction fs as [| f fs]; simpl.
    trivial.
    intro. rewrite map_app, map_map. f_equal. apply IHfs.
Qed.

Lemma ap_list_exchange3 :
  forall (A B C : Type) (f : A -> B) (fs : list (A -> B)) (gs : list (B -> C))
  (xs : list A),
    ap_list (ap_list (map compose gs) (f :: fs)) xs =
    ap_list gs (map f xs ++ ap_list fs xs).
Proof.
  induction gs as [| g gs]; simpl.
    trivial.
    intro. rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app. rewrite ap_list_exchange2. f_equal.
        rewrite IHgs. trivial.
Qed.

Instance Applicative_List : Applicative list :=
{
    is_functor := FunctorList;
    pure := @pure_List; 
    ap := @ap_list
}.
Proof.
  induction ax; cbn in *; rewrite ?IHax; reflexivity.
  induction af as [| f fs]; induction ag as [| g gs]; cbn; intros.
    trivial.
    repeat rewrite ap_list_nil_r. cbn. trivial.
    trivial.
    rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app. f_equal.
        apply ap_list_exchange2.
        rewrite app_nil_r. apply ap_list_exchange3.
  cbn. trivial.
  induction f as [| f fs]; cbn in *; intros; rewrite ?IHfs; reflexivity.
  cbn; intros. unfold fmap_List. rewrite app_nil_r. reflexivity.
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

Fixpoint bind_List {A B : Type} (la : list A) (f : A -> list B) : list B :=
match la with
    | [] => []
    | h :: t => f h ++ bind_List t f
end.

Lemma bind_List_app :
  forall (A B : Type) (l1 l2 : list A) (f : A -> list B),
    bind_List (l1 ++ l2) f = bind_List l1 f ++ bind_List l2 f.
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1, app_assoc. trivial.
Qed.

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
  all: cbn.
  intros. rewrite app_nil_r. reflexivity.
  induction ma as [| h t]; cbn; rewrite ?IHt; reflexivity.
  induction ma as [| h t]; cbn; intros.
    trivial.
    rewrite bind_List_app, <- IHt. trivial.
  induction mf as [| hf tf]; cbn; intros.
    reflexivity.
    rewrite <- IHtf. f_equal. induction mx as [| h t]; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Defined.

Instance MonadPlus_List : MonadPlus list :=
{
    is_monad := Monad_List;
    is_alternative := Alternative_List;
}.
Proof. monad. Defined.

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