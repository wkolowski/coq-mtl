Require Import Control.

Inductive Vec (A : Type) : nat -> Type :=
    | vnil : Vec A 0
    | vcons : forall n : nat, A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Fixpoint fmap_Vec
  {A B : Type} {n : nat} (f : A -> B) (va : Vec A n) : Vec B n :=
match va with
    | vnil => vnil
    | vcons h t => vcons (f h) (fmap_Vec f t)
end.

Fixpoint pure_Vec
  {A : Type} {n : nat} (x : A) : Vec A n :=
match n with
    | 0 => vnil
    | S n' => vcons x (@pure_Vec A n' x)
end.

Fixpoint ap_Vec
  {A B : Type} {n : nat} (f : Vec (A -> B) n) (x : Vec A n) : Vec B n.
Proof.
  destruct f as [| n f fs].
    exact vnil.
    inv x. exact (vcons (f X) (ap_Vec _ _ _ fs X0)).
Defined.

Require Import Coq.Program.Equality.

Fixpoint ap_Vec2
  {A B : Type} {n : nat} (f : Vec (A -> B) n) : Vec A n -> Vec B n.
Proof.
  destruct f as [| n f fs]; intro x.
    exact vnil.
    dependent destruction x. exact (vcons (f a) (ap_Vec2 _ _ _ fs x)).
Defined.
Check @vcons.
(*
Fixpoint ap_Vec3
  {A B : Type} {n : nat} (f : Vec (A -> B) n) (x : Vec A n) : Vec B n :=
match f, x with
    | vnil, _ => vnil
    | vcons f fs, vcons x xs => vcons (f x) (ap_Vec3 fs xs)
end.
*)

Fixpoint ap_Vec3
  {A B : Type} {n : nat} (f : Vec (A -> B) n) : Vec A n -> Vec B n :=
  let diag (n : nat) :=
    match n with
        | 0 => unit
        | S n' => Vec B (S n')
    end
  in
  match f with
    | vnil => fun _ => vnil
    | @vcons _ nfs f fs => fun v : Vec A (S nfs) =>
        match v in Vec _ m return nfs = pred m -> diag m with
          | vnil => fun _ => tt
          | @vcons _ nxs x xs => fun p : nfs = nxs =>
              match p in (_ = nxs) return Vec A nxs -> Vec B (S nxs) with
                  | eq_refl => fun xs' => vcons (f x) (ap_Vec3 fs xs')
              end xs
        end eq_refl
  end.

Print ap_Vec.
Print ap_Vec2.
Print ap_Vec3.

(*
Fixpoint bind_Vec
  {A B : Type} {n : nat} (x : Vec A n) (f : A -> Vec B n)
*)

Definition Vec' n A := Vec A n.

Definition fmap_Vec' {n : nat} {A B : Type} := @fmap_Vec A B n.

Hint Unfold fmap_Vec fmap_Vec' : HSLib.

Instance Functor_Vec' (n : nat) : Functor (Vec' n) :=
{
    fmap := @fmap_Vec' n
}.
Proof.
  intro A. ext v. induction v; cbn.
    reflexivity.
    unfold fmap_Vec' in IHv. rewrite IHv. reflexivity.
  intros A B C f g. ext v. induction v; cbn.
    reflexivity.
    unfold fmap_Vec' in IHv. rewrite IHv. unfold compose. reflexivity.
Defined.

Definition pure_Vec' {n : nat} {A : Type} := @pure_Vec A n.
Definition ap_Vec'
  {n : nat} {A B : Type} (f : Vec' n (A -> B)) (x : Vec' n A) : Vec' n B :=
    @ap_Vec3 A B n f x.

Hint Unfold pure_Vec' ap_Vec' : HSLib.

Check pure_Vec'.
Check ap_Vec'.

(*
Instance Applicative_Vec' (n : nat) : Applicative (Vec' n) :=
{
    pure := @pure_Vec' n;
    ap := @ap_Vec' n;
}.
Proof.
  all: unfold pure_Vec', ap_Vec'.
  induction ax; cbn.
    reflexivity.
    rewrite IHax. reflexivity.
  induction ag; cbn; intros.
    reflexivity.
    dependent inversion af.
    intros.
  induction n as [| n']; cbn; intros.
    assert (ag = vnil).
      dependent inversion ag.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
  induction f as [| n f fs]; cbn; intros.
    reflexivity.
    rewrite IHfs. reflexivity.
  induction x; cbn.
    reflexivity.
    rewrite <- IHx. reflexivity.
Defined.
*)