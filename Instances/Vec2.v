Require Import Control.

Inductive Vec (A : Type) : nat -> Type :=
    | vnil : Vec A 0
    | vcons : forall n :nat, A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Fixpoint fmap_Vec
  {A B : Type} {n : nat} (f : A -> B) (va : Vec A n) : Vec B n :=
match va with
    | vnil => vnil
    | vcons h t => vcons (f h) (fmap_Vec f t)
end.

Definition Vec' n A := Vec A n.

(*
Instance Functor_Vec (n : nat) : Functor (Vec' n) :=
{
    fmap := fmap_Vec
}.
Proof.
  intros. ext va. induction va; cbn.
    reflexivity.
    rewrite IHva. reflexivity.
  intros. ext va. induction va; cbn.
    reflexivity.
    rewrite IHva. reflexivity.
Defined.

Print Functor_Vec.

Fixpoint pure_Vec {n : nat} {A : Type} (x : A) : Vec n A :=
match n with
    | 0 => vnil
    | S n' => vcons x (@pure_Vec n' A x)
end.

Fixpoint ap_Vec
  {n : nat} {A B : Type} (vf : Vec n (A -> B)) : Vec n A -> Vec n B.
Proof.
  inv vf.
    intros _. exact vnil.
    rename X into f. rename X0 into fs. intro va. inv va.
      rename X into x. rename X0 into xs.
      exact (vcons (f x) (ap_Vec _ _ _ fs xs)).
Defined.

Print Applicative.
Print Monad.
Print Applicative.
Print Vec.

Instance Applicative_Vec (n : nat) : Applicative (Vec n).
Abort.
*)