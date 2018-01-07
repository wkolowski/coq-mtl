Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition State (S A : Type) := S -> A * S.

Definition fmap_State
  (S A B : Type) (f : A -> B) (st : State S A) : State S B :=
    fun s : S => let (a, s') := st s in (f a, s').

Instance FunctorState (S : Type) : Functor (State S) :=
{
    fmap := @fmap_State S
}.
Proof.
  all: intros; ext x; ext s; compute; destruct (x s); reflexivity.
Defined.

Definition ret_State
  (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

Definition ap_State
  (S A B : Type) (sf : State S (A -> B)) (sa : State S A) : State S B :=
    fun st : S =>
      let (f, stf) := sf st in
      let (a, sta) := sa stf in (f a, sta).

Instance ApplicativeState (S : Type) : Applicative (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    ap := @ap_State S
}.
Proof.
  intros. unfold ret_State, ap_State. extensionality st.
    destruct (ax st). trivial.
  intros. unfold ret_State, ap_State. unfold State in *. extensionality st.
    destruct (ag st). destruct (af s). destruct (ax s0). trivial.
  intros. unfold ret_State, ap_State. extensionality st. trivial.
  intros. unfold ret_State, ap_State. extensionality st. destruct (f st).
    trivial.
Restart.
  all: intros; compute; ext st.
    destruct (ax st). reflexivity.
    destruct (ag st), (af s), (ax s0). reflexivity.
    reflexivity.
    destruct (f st). reflexivity.
    destruct (x st). reflexivity.
Defined.

Theorem State_not_alternative :
  (forall S : Type, Alternative (State S)) -> False.
Proof.
  unfold State. intro. destruct (X unit). destruct (aempty False tt).
  assumption.
Qed.

Definition join_State
  {S A : Type} (ssa : State S (State S A)) : State S A :=
    fun s : S => let (f, s') := ssa s in f s'.

Definition bind_State
  {S A B : Type} (sa : State S A) (f : A -> State S B)
    : State S B := fun s : S => let (a, s') := sa s in f a s'.

Definition compM_State
  {S A B C : Type} (f : A -> State S B) (g : B -> State S C) (a : A)
    : State S C := fun s : S => let (b, s') := f a s in g b s'.