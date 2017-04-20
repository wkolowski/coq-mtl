Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Definition State (S A : Type) := S -> A * S.

Definition fmap_State (S A B : Type) (f : A -> B) (st : State S A)
    : State S B := fun s : S => let (a, s') := st s in (f a, s').

Definition ret_State (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

Definition ap_State (S A B : Type) (sf : State S (A -> B)) (sa : State S A)
    : State S B := fun st : S =>
        let (f, stf) := sf st in
        let (a, sta) := sa stf in (f a, sta).

Definition join_State {S A : Type} (ssa : State S (State S A)) : State S A :=
    fun s : S => let (f, s') := ssa s in f s'.