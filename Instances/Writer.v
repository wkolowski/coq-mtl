Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Require Export HSLib.Monoid.

Definition Writer (W : Monoid) (A : Type) : Type := (A * W)%type.

Ltac solveWriter' :=
repeat match goal with
    | w : Writer _ _ |- _ => destruct w
    | |- context [let (_, _) := ?f ?x in _] => destruct (f x)
    | |- _ = _ => let id := fresh in extensionality id
    | _ => rewrite ?id_left, ?id_right, ?op_assoc; eauto
end.

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
  all: intros; unfold fmap_Writer, id; solveWriter'.
Defined.

Definition ret_Writer
  {W : Monoid} {A : Type} (a : A) : Writer W A := (a, neutr).

Definition ap_Writer
  {W : Monoid} {A B : Type} (wf : Writer W (A -> B)) (wa : Writer W A)
    : Writer W B := let '((f, w), (a, w')) := (wf, wa) in (f a, op w w').

Instance ApplicativeWriter (W : Monoid) : Applicative (Writer W) :=
{
    is_functor := FunctorWriter W;
    ret := @ret_Writer W;
    ap := @ap_Writer W
}.
Proof.
  all: intros; unfold ret_Writer, ap_Writer, id; solveWriter'.
Defined.

Theorem Writer_not_alternative :
  forall W : Monoid, Alternative (Writer W) -> False.
Proof.
  destruct 1. destruct (aempty False). assumption.
Qed.

Definition join_Writer
  {W : Monoid} {A : Type} (wwa : Writer W (Writer W A)) : Writer W A :=
    let '((a, w), w') := wwa in (a, op w w').

Definition bind_Writer
  {W : Monoid} {A B : Type} (wa : Writer W A) (f : A -> Writer W B)
    : Writer W B :=
      let (a, w) := wa in
      let (b, w') := f a in (b, op w w').

Definition compM_Writer
  {W : Monoid} {A B C : Type} (f : A -> Writer W B) (g : B -> Writer W C)
    (x : A) : Writer W C :=
      let (b, w) := f x in
      let (c, w') := g b in (c, op w w').

Ltac solveWriter :=
  cbn; intros;
  unfold
    fmap_Writer, ret_Writer, ap_Writer, join_Writer, bind_Writer,
    compM_Writer, id, compose;
  solveWriter'.