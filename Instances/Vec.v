Add Rec LoadPath "~/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.Foldable.

Polymorphic Cumulative Inductive Vec : nat -> Type -> Type :=
    | vnil : forall A : Type, Vec 0 A
    | vcons : forall (n : nat) (A : Type), A -> Vec n A -> Vec (S n) A.

Arguments vnil {A}.
Arguments vcons {n} {A}.

Fixpoint fmap_Vec
  {n : nat} {A B : Type} (f : A -> B) (va : Vec n A) : Vec n B.
Proof.
  destruct va as [| n A h t].
    exact vnil.
    exact (vcons (f h) (fmap_Vec n A B f t)).
Defined.

Instance Functor_Vec (n : nat) : Functor (Vec n) :=
{
    fmap := @fmap_Vec n
}.
Proof.
  intros. ext va. induction va; cbn.
    reflexivity.
    rewrite IHva. reflexivity.
  intros. ext va. induction va; cbn.
    reflexivity.
    rewrite IHva. reflexivity.
Defined.

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

Instance Applicative_Vec (n : nat) : Applicative (Vec n) :=
{
    pure := @pure_Vec n;
    ap := @ap_Vec n;
}.