Require Import Control.

(* Rose Trees *)
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

Theorem RT_not_MonadPlus :
  MonadPlus RT -> False.
Proof.
  destruct 1. apply RT_not_Alternative. assumption.
Qed.

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

Instance MonadAlt_RT : MonadAlt RT Monad_RT :=
{
    choose := @Node
}.
Proof.
  
  Focus 2. reflexivity.
Abort.