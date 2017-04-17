Add LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export HSLib.Applicative.Applicative.
Require Export HSLib.Functor.FunctorInst.

Instance ApplicativeOption : Applicative option :=
{
    is_functor := FunctorOption;
    ret := Some;
    ap := fun {A B : Type} (of : option (A -> B)) (oa : option A) =>
        match of, oa with
            | Some f, Some a => Some (f a)
            | _, _ => None
        end
}.
Proof.
  intros. unfold id. destruct ax; trivial.
  intros. destruct ax, af, ag; trivial.
  intros. trivial.
  intros. destruct f; trivial.
Defined.
Require Import List.

Definition ap_list' {A B : Type} (lf : list (A -> B)) (la : list A)
    : list B := fold_right (fun f bs => fmap f la ++ bs) [] lf.

Fixpoint ap_list {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
match lf with
    | [] => []
    | f :: fs => fmap f la ++ ap_list fs la
end.

Theorem ap_list_nil_l : forall (A B : Type) (la : list A),
    ap_list [] la = @nil B.
Proof.
  simpl. trivial.
Qed.

Theorem ap_list_nil_r : forall (A B : Type) (lf : list (A -> B)),
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

Theorem ap_list_map : forall (A B : Type) (f : A -> B) (la : list A),
    ap_list [f] la = map f la.
Proof.
  (*intros. simpl. rewrite app_nil_r. trivial.*)
  induction la as [| x xs]; simpl in *.
    trivial.
    rewrite IHxs. trivial.
Qed.

Theorem ap_list_exchange : forall (A B : Type) (x : A) (lf : list (A -> B)),
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

Theorem ap_list_exchange3 : forall (A B C : Type) (f : A -> B)
    (fs : list (A -> B)) (gs : list (B -> C)) (xs : list A),
        ap_list (ap_list (map compose gs) (f :: fs)) xs =
        ap_list gs (map f xs ++ ap_list fs xs).
Proof.
  induction gs as [| g gs]; simpl.
    trivial.
    intro. rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app. rewrite ap_list_exchange2. f_equal.
        rewrite IHgs. trivial.
Qed.

Fixpoint ap_list2 {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
match la with
    | [] => []
    | h :: t => map (fun f => f h) lf ++ ap_list2 lf t
end.

Theorem ap_list2_nil_l : forall (A B : Type) (la : list A),
    ap_list2 [] la = @nil B.
Proof.
  induction la; auto.
Qed.

Theorem ap_list2_nil_r : forall (A B : Type) (lf : list (A -> B )),
    ap_list2 lf [] = [].
Proof.
  induction lf as [| f fs]; auto.
Qed.

Theorem ap_list2_app :
    forall (A B : Type) (lf : list (A -> B)) (la la' : list A),
        ap_list2 lf (la ++ la') = ap_list2 lf la ++ ap_list2 lf la'.
Proof.
  induction la as [| x xs]; intros; simpl.
    trivial.
    rewrite <- app_assoc. rewrite IHxs. trivial.
Qed.

Theorem ap_list2_map : forall (A B : Type) (f : A -> B) (la : list A),
    ap_list2 [f] la = map f la.
Proof.
  induction la as [| h t]; simpl; try rewrite IHt; trivial.
Qed.

Theorem ap_list2_exchange : forall (A B : Type) (x : A) (lf : list (A -> B)),
    ap_list2 [fun f : A -> B => f x] lf = ap_list2 lf [x].
Proof.
  induction lf as [| f fs].
    simpl. trivial.
    simpl. rewrite IHfs. simpl. trivial.
Qed.

Instance ApplicativeList : Applicative list :=
{
    is_functor := FunctorList;
    ret := fun {A : Type} (x : A) => [x];
    ap := @ap_list
}.
Proof.
  intros. induction ax.
    simpl. trivial.
    simpl in *. rewrite IHax. trivial.
  Focus 2. simpl. trivial.
  Focus 2. intros. induction f as [| f fs].
    simpl. trivial.
    simpl in *. rewrite IHfs. trivial. simpl.
  induction af as [| f fs]; induction ag as [| g gs]; simpl; intros.
    trivial.
    repeat rewrite ap_list_nil_r. simpl. trivial.
    trivial.
    rewrite map_app, map_map, <- app_assoc. f_equal.
      rewrite ap_list_app. f_equal.
        apply ap_list_exchange2.
        rewrite app_nil_r. apply ap_list_exchange3.
Defined.