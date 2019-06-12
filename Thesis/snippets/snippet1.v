Print nat.
(*
Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.
*)

Inductive Tree (A : Type) : Type :=
    | Leaf : A -> Tree A
    | Node : Tree A -> Tree A -> Tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint label
  {A : Type} (t : Tree A) (n : nat) : nat * Tree (A * nat) :=
match t with
    | Leaf x => (n, Leaf (x, n))
    | Node l r =>
        let (n', l') := label l n in
        let (n'', r') := label r (S n') in
          (n'', Node  l' r')
end.

Definition lbl {A : Type} (t : Tree A) : Tree (A * nat) :=
  snd (label t 0).

Compute lbl (Node (Node (Leaf true) (Leaf true)) (Leaf false)).
(* = Node (Node (Leaf (true, 0)) (Leaf (true, 1))) (Leaf (false, 2))
   : Tree (bool * nat) *)

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | Leaf _ => 1
    | Node l r => size l + size r
end.

Require Import Arith.

Theorem label_size :
  forall (A : Type) (t : Tree A) (n n' : nat) (t' : Tree (A * nat)),
    label t n = (n', t') -> S n' = n + size t.
Proof.
  induction t as [| l IHl r IHr]; intros.
    rewrite <- plus_comm. cbn. inversion H. reflexivity.
    cbn. intros.
      case_eq (label l n); intros m1 t1 H1.
      case_eq (label r (S m1)); intros m2 t2 H2.
      rewrite H1, H2 in H. inversion H; subst.
      rewrite (IHr _ _ _ H2), (IHl _ _ _ H1), plus_assoc. reflexivity.
Qed.