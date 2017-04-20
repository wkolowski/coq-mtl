Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Monoid.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadJoin.Monad.

Definition Writer (W : Monoid) (A : Type) : Type := prod A W.

Definition fmap_Writer {W : Monoid} {A B : Type} (f : A -> B) (wa : Writer W A)
    : Writer W B :=
match wa with
    | (a, w) => (f a, w)
end.

Instance FunctorWriter (W : Monoid) : Functor (Writer W) :=
{
    fmap := @fmap_Writer W
}.
Proof.
  intro. unfold fmap_Writer, id. extensionality wa. destruct wa; trivial.
  intros. unfold fmap_Writer, id. extensionality wa. destruct wa; trivial.
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

Definition join_Writer {W : Monoid} {A : Type} (wwa : Writer W (Writer W A))
    : Writer W A :=
match wwa with
    | pair (pair a w) w' => pair a (op w w')
end.

Ltac solveWriter := simpl; intros;
    unfold fmap_Writer, ret_Writer, ap_Writer, join_Writer, id, compose;
repeat match goal with
    | wx : Writer _ _ |- _ => destruct wx
    | |- _ = _ => let id := fresh in extensionality id
    | _ => try rewrite id_left;
        try rewrite id_right; try rewrite op_assoc; eauto
end.

Instance MonadWriter (W : Monoid) : Monad (Writer W) :=
{
    ret := @ret_Writer W;
    join := @join_Writer W
}.
Proof.
  * intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wwwx. destruct wwwx as [[[x w] w'] w''].
    rewrite op_assoc. trivial.
  * intros. simpl. unfold fmap_Writer, ret_Writer, join_Writer, id, compose.
    extensionality wx. destruct wx as [x w]. rewrite id_left, id_right. auto.
Defined.