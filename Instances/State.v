Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.

Definition State (S A : Type) := S -> A * S.

Definition fmap_State
  (S A B : Type) (f : A -> B) (st : State S A) : State S B :=
    fun s : S => let (a, s') := st s in (f a, s').

Hint Unfold State fmap_State compose : HSLib.

Instance FunctorState (S : Type) : Functor (State S) :=
{
    fmap := @fmap_State S
}.
Proof. all: monad. Defined.

Definition ret_State
  (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

Definition ap_State
  (S A B : Type) (sf : State S (A -> B)) (sa : State S A) : State S B :=
    fun st : S =>
      let (f, stf) := sf st in
      let (a, sta) := sa stf in (f a, sta).

Hint Unfold ret_State ap_State : HSLib.

Instance ApplicativeState (S : Type) : Applicative (State S) :=
{
    is_functor := FunctorState S;
    ret := @ret_State S;
    ap := @ap_State S
}.
Proof. all: monad. Defined.

Theorem State_not_CommutativeApplicative :
  ~ (forall S : Type, CommutativeApplicative _ (ApplicativeState S)).
Proof.
  intro. destruct (H bool). compute in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (fun b => if b then (42, negb b) else (142, b))
    (fun b => if b then (143, b) else (43, negb b))).
  apply (@f_equal _ _ (fun f => f true)) in ap_comm.
  cbn in ap_comm. congruence.
Qed.

Theorem State_not_alternative :
  (forall S : Type, Alternative (State S)) -> False.
Proof.
  unfold State. intro. destruct (X unit). destruct (aempty False tt).
  assumption.
Qed.

Definition bind_State
  {S A B : Type} (sa : State S A) (f : A -> State S B)
    : State S B := fun s : S => let (a, s') := sa s in f a s'.

Hint Unfold bind_State : HSLib.

Instance Monad_State (S : Type) : Monad (State S) :=
{
    is_applicative := ApplicativeState S;
    bind := @bind_State S
}.
Proof. all: monad. Defined.

(* TODO *) Require Import HSLib.MonadClass.MonadState.
Instance MonadState_State
  (S : Type) : MonadState S (State S) (Monad_State S) :=
{
    get := fun s : S => (s, s);
    put := fun s : S => fun _ => (tt, s)
}.
Proof. all: hs. Defined.