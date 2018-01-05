Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Require Export HSLib.Monoid.

Definition Writer (W : Monoid) (A : Type) : Type := (A * W)%type.

Definition fmap_Writer
  {W : Monoid} {A B : Type} (f : A -> B) (wa : Writer W A) : Writer W B :=
match wa with
    | (a, w) => (f a, w)
end.

Instance FunctorWriter (W : Monoid) : Functor (Writer W) :=
{
    fmap := @fmap_Writer W
}.
Proof.
  all: intros; unfold fmap_Writer, id; ext wa; destruct wa; reflexivity.
Defined.

Definition ret_Writer {W : Monoid} {A : Type} (a : A) : Writer W A :=
  (a, neutr).

Definition ap_Writer {W : Monoid} {A B : Type} (wf : Writer W (A -> B))
    (wa : Writer W A) : Writer W B :=
match wf, wa with
    | pair f w, pair a w' => pair (f a) (op w w')
end.

Instance ApplicativeWriter (W : Monoid) : Applicative (Writer W) :=
{
    is_functor := FunctorWriter W;
    ret := @ret_Writer W;
    ap := @ap_Writer W
}.
Proof.
  intros. unfold ret_Writer, ap_Writer, id. destruct ax.
    rewrite id_left. trivial.
  intros. unfold ret_Writer, ap_Writer, id. destruct af, ag, ax.
    rewrite id_left, op_assoc. trivial.
  intros. unfold ret_Writer, ap_Writer, id. rewrite id_left. trivial.
  intros. unfold ret_Writer, ap_Writer, id. destruct f.
    rewrite id_left, id_right. trivial.
Defined.

Theorem Writer_not_alternative : forall W : Monoid,
    Alternative (Writer W) -> False.
Proof.
  destruct 1. destruct (aempty False). assumption.
Qed.

Definition join_Writer {W : Monoid} {A : Type} (wwa : Writer W (Writer W A))
    : Writer W A :=
match wwa with
    | pair (pair a w) w' => pair a (op w w')
end.

Definition bind_Writer
  {W : Monoid} {A B : Type} (wa : Writer W A) (f : A -> Writer W B)
    : Writer W B :=
      let (a, w) := wa in
      let (b, w') := f a in (b, op w w').

Definition compM_Writer {W : Monoid} {A B C : Type}
    (f : A -> Writer W B) (g : B -> Writer W C) (x : A) : Writer W C :=
    let (b, w) := f x in
    let (c, w') := g b in (c, op w w').

Ltac solveWriter := simpl; intros;
    unfold fmap_Writer, ret_Writer, ap_Writer, join_Writer, bind_Writer,
    compM_Writer, id, compose;
repeat match goal with
    | wx : Writer _ _ |- _ => destruct wx
    | |- context [let (_, _) := ?f ?x in _] => destruct (f x)
    | |- _ = _ => let id := fresh in extensionality id
    | _ => try rewrite id_left;
        try rewrite id_right; try rewrite op_assoc; eauto
end.