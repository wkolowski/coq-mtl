Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition fmap_List := map.

Instance FunctorList : Functor list :=
{
    fmap := fmap_List
}.
Proof.
  all: cbn; unfold fmap_List, id, compose; intros; ext l.
    apply map_id.
    rewrite <- map_map. reflexivity.
Defined.

Definition ret_List {A : Type} (x : A) : list A := [x].

Fixpoint ap_list {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
match lf with
    | [] => []
    | f :: fs => map f la ++ ap_list fs la
end.

Theorem ap_list_nil_l :
  forall (A B : Type) (la : list A),
    @ap_list A B [] la = [].
Proof. cbn. reflexivity. Qed.

Theorem ap_list_nil_r :
  forall (A B : Type) (lf : list (A -> B)),
    ap_list lf [] = [].
Proof.
  induction lf as [| f fs]; auto.
Qed.

Theorem ap_list_app :
  forall (A B : Type) (lf lf' : list (A -> B)) (la : list A),
      ap_list (lf ++ lf') la = ap_list lf la ++ ap_list lf' la.
Proof.
  induction lf as [| f fs]; intros; simpl.
    trivial.
    rewrite <- app_assoc. rewrite IHfs. trivial.
Qed.

Theorem ap_list_map :
  forall (A B : Type) (f : A -> B) (la : list A),
    ap_list [f] la = map f la.
Proof.
  induction la as [| x xs]; simpl in *.
    trivial.
    rewrite IHxs. trivial.
Qed.

Theorem ap_list_exchange :
  forall (A B : Type) (x : A) (lf : list (A -> B)),
    ap_list [fun f : A -> B => f x] lf = ap_list lf [x].
Proof.
  induction lf as [| f fs]; simpl in *.
    trivial.
    rewrite IHfs. trivial.
Qed.

Theorem ap_list_exchange2 :
  forall (A B C : Type) (g : B -> C) (fs : list (A -> B)) (xs : list A),
      ap_list (map (compose g) fs) xs = map g (ap_list fs xs).
Proof.
  induction fs as [| f fs]; simpl.
    trivial.
    intro. rewrite map_app, map_map. f_equal. apply IHfs.
Qed.

Theorem ap_list_exchange3 :
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

Instance ApplicativeList : Applicative list :=
{
    is_functor := FunctorList;
    ret := @ret_List; 
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

Instance AlternativeList : Alternative list :=
{
    is_applicative := ApplicativeList;
    aempty := @aempty_List;
    aplus := @aplus_List
}.
Proof.
  apply app_nil_l.
  apply app_nil_r.
  apply app_assoc.
Defined.

Fixpoint join_List {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | hl :: tll => hl ++ join_List tll
end.

Fixpoint bind_List {A B : Type} (la : list A) (f : A -> list B) : list B :=
match la with
    | [] => []
    | h :: t => f h ++ bind_List t f
end.

Definition compM_List
  {A B C : Type} (f : A -> list B) (g : B -> list C) (x : A) : list C :=
    bind_List (f x) g.

Theorem bind_List_app :
    forall (A B : Type) (l1 l2 : list A) (f : A -> list B),
        bind_List (l1 ++ l2) f = bind_List l1 f ++ bind_List l2 f.
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1, app_assoc. trivial.
Qed.