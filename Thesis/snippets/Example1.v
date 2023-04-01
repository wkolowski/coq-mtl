Inductive Tree (A : Type) : Type :=
| Leaf : A -> Tree A
| Node : Tree A -> Tree A -> Tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
| Leaf _ => 1
| Node l r => size l + size r
end.

Require Import Arith.

From CoqMTL Require Import Control.Monad.Class.MonadState.

Fixpoint label
  {M : Type -> Type} {inst : Monad M} {instS : MonadState nat M inst}
  {A : Type} (t : Tree A) : M (Tree (A * nat)) :=
match t with
| Leaf x => do
    n <- get;
    pure $ Leaf (x, n)
| Node l r => do
    l' <- label l;
    modify S;;
    r' <- label r;
    pure $ Node l' r'
end.

From CoqMTL Require Import Control.Monad.State.

Definition lbl {A : Type} (t : Tree A) : Tree (A * nat) :=
  fst (@label (State nat) _ _ _ t 0).

Compute lbl (Node (Node (Leaf true) (Leaf true)) (Leaf false)).
(* = Node (Node (Leaf (true, 0)) (Leaf (true, 1))) (Leaf (false, 2))
   : Tree (bool * nat) *)

Theorem label_size :
  forall (A : Type) (t : Tree A) (n : nat),
    1 + snd (@label (State nat) _ _ _ t n) = n + size t.
Proof.
  induction t as [| l IHl r IHr]; hs.
  - rewrite <- plus_comm. reflexivity.
  - case_eq (label l n); intros t1 m1 H1.
    case_eq (label r (S m1)); intros t2 m2 H2.
    specialize (IHl n). specialize (IHr (S m1)).
    rewrite H1, H2 in *. cbn in *.
    rewrite IHr, <- plus_Sn_m, IHl, !plus_assoc. reflexivity.
Qed.