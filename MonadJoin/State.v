Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import Applicative.
Require Import HSLib.MonadJoin.Monad.

Definition State (S A : Type) := S -> A * S.

Instance FunctorState (S : Type) : Functor (State S) :=
{
    fmap := fun (A B : Type) (f : A -> B) (st : State S A) =>
      fun s : S => let (a, s') := st s in (f a, s')
}.
Proof.
  intros. extensionality st. extensionality s. unfold id.
    destruct (st s). reflexivity.
  intros. extensionality st. extensionality s. unfold compose, id.
    destruct (st s). reflexivity.
Defined.

Instance ApplicativeState (S : Type) : Applicative (State S) :=
{
    is_functor := FunctorState S;
    ret := fun (A : Type) (a : A) =>
        fun s : S => (a, s);
    ap := fun (A B : Type) (sf : State S (A -> B)) (sa : State S A) =>
        fun st : S =>
            let (f, stf) := sf st in
            let (a, sta) := sa stf in
            (f a, sta)
}.
Proof.
  intros. extensionality st. destruct (ax st). trivial.
  Focus 2. intros. extensionality st. trivial.
  Focus 2. intros. extensionality st. destruct (f st). trivial.
  intros. unfold State in *. extensionality st.
    destruct (ag st). destruct (af s). destruct (ax s0). trivial.
Defined.

Definition retS (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

Definition joinS {S A : Type} (ssa : State S (State S A)) : State S A :=
    fun s : S => let (f, s') := ssa s in f s'.

Instance MonadState (S : Type) : Monad (State S) :=
{
    is_functor := FunctorState S;
    ret := retS S;
    join := @joinS S
}.
Proof.
  intros. extensionality s3x. extensionality s1.
    simpl. unfold joinS. unfold compose. destruct (s3x s1).
    destruct (s s0). trivial.
  intros. extensionality sx. extensionality s.
    simpl. unfold joinS, retS. unfold compose.
    destruct (sx s). trivial.
Defined.