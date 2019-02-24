Require Import Control.
Require Import Misc.Monoid.

(** Rose Trees - trees which hold values in their leaves. *)
Inductive RT (A : Type) : Type :=
    | Leaf : A -> RT A
    | Node : RT A -> RT A -> RT A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint fmap_RT {A B : Type} (f : A -> B) (t : RT A) : RT B :=
match t with
    | Leaf x => Leaf (f x)
    | Node l r => Node (fmap_RT f l) (fmap_RT f r)
end.

Instance Functor_RT : Functor RT :=
{
    fmap := @fmap_RT
}.
Proof.
  all: intros; ext t;
  induction t as [x | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
Defined.

Definition pure_RT {A : Type} (x : A) : RT A := Leaf x.

Fixpoint ap_RT {A B : Type} (tf : RT (A -> B)) (ta : RT A) : RT B :=
match tf with
    | Leaf f => fmap f ta
    | Node l r => Node (ap_RT l ta) (ap_RT r ta)
end.

Instance Applicative_RT : Applicative RT :=
{
    pure := @pure_RT;
    ap := @ap_RT;
}.
Proof.
  all: cbn; intros.
    cbn. rewrite (@fmap_id _ Functor_RT). reflexivity.
    induction ag as [g | gl IHgl gr IHgr]; cbn.
      induction af as [f | fl IHfl fr IHfr]; cbn.
        rewrite (@fmap_comp' _ Functor_RT). reflexivity.
        rewrite IHfl, IHfr. reflexivity.
      rewrite IHgl, IHgr. reflexivity.
    reflexivity.
    induction f as [f | l IHl r IHr]; cbn; rewrite ?IHl, ?IHr; reflexivity.
    reflexivity.
Defined.

Theorem RT_not_CommutativeApplicative :
  ~ CommutativeApplicative _ Applicative_RT.
Proof.
  destruct 1.
  specialize (ap_comm bool bool _ (fun _ => id)
    (Node (Leaf false) (Leaf true)) (Node (Leaf true) (Leaf false))).
  compute in *. congruence.
Qed.

Theorem RT_not_Alternative :
  Alternative RT -> False.
Proof.
  destruct 1. induction (aempty False); contradiction.
Qed.

Fixpoint bind_RT {A B : Type} (ta : RT A) (tf : A -> RT B) : RT B :=
match ta with
    | Leaf x => tf x
    | Node l r => Node (bind_RT l tf) (bind_RT r tf)
end.

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

(*Hint Unfold fmap_RT pure_RT ap_RT bind_RT : HSLib.*)

Fixpoint foldMap_RT
  {A : Type} {M : Monoid} (f : A -> M) (t : RT A) : M :=
match t with
    | Leaf x => f x
    | Node l r => op (foldMap_RT f l) (foldMap_RT f r)
end.

Instance Foldable_RT : Foldable RT :=
{
    foldMap := @foldMap_RT
}.
Proof.
  intros. ext t.
  induction t as [| l IHl r IHr]; unfold compose in *; cbn; congruence.
Defined.

Require Import Control.Monad.Class.All.

Module nel.

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | ncons : A -> nel A -> nel A.

Arguments singl {A}.
Arguments ncons {A}.

(*
Fixpoint leftmost {A : Type} (t : RT A) : A * option (RT A) :=
match t with
    | Leaf a => (a, None)
    | Node l r =>
        match leftmost l with
            | (a, None) => (a, Some r)
            | (a, Some l') => (a, Some (Node l' r))
        end
end.
*)

Fixpoint napp {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl a => ncons a l2
    | ncons h t => ncons h (napp t l2)
end.

Fixpoint toNel {A : Type} (t : RT A) : nel A :=
match t with
    | Leaf a => singl a
    | Node l r => napp (toNel l) (toNel r)
end.

Fixpoint fromNel {A : Type} (l : nel A) : RT A :=
match l with
    | singl a => Leaf a
    | ncons h t => Node (Leaf h) (fromNel t)
end.

Definition flatten {A : Type} (t : RT A) : RT A :=
  fromNel (toNel t).

Lemma toNel_fromNel :
  forall (A : Type) (l : nel A),
    toNel (fromNel l) = l.
Proof.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

Lemma napp_assoc :
  forall (A : Type) (l1 l2 l3 : nel A),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
Proof.
  induction l1; cbn; intros; rewrite ?IHl1; reflexivity.
Qed.

Instance MonadAlt_RT : MonadAlt RT Monad_RT :=
{
    choose := fun A x y => flatten (Node x y)
}.
Proof.
  induction a; cbn; intros;
    rewrite !toNel_fromNel, ?napp_assoc; reflexivity.
  induction x; cbn; intros.
    induction y; cbn.
Abort.

End nel.