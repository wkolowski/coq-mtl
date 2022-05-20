Require Import Control.All.
Require Import Control.Monad.Class.All.

(** [State S A] models a computation which returns a result of type [A]
    and has read and write access to a single cell of state of type [S]. *)
Definition State (S A : Type) := S -> A * S.

(** We can map over such a computation by applying a function to its
    result without touching the state. *)
Definition fmap_State
  (S A B : Type) (f : A -> B) (st : State S A) : State S B :=
    fun s : S => let (a, s') := st s in (f a, s').

#[global] Hint Unfold fmap_State : CoqMTL.

#[refine]
#[export]
Instance Functor_State (S : Type) : Functor (State S) :=
{
    fmap := @fmap_State S
}.
Proof. all: unfold compose; monad. Defined.

(** We can inject a value into the monad by returning it without changing
    the state. *)
Definition pure_State
  (S A : Type) : A -> State S A :=
    fun (a : A) (s : S) => (a, s).

(** We can apply a stateful function to a stateful argument by running
    the computations in this order and then applying the function to
    the argument. The resulting state is that obtained from computing
    the argument. *)
Definition ap_State
  (S A B : Type) (sf : State S (A -> B)) (sa : State S A) : State S B :=
    fun st : S =>
      let (f, stf) := sf st in
      let (a, sta) := sa stf in (f a, sta).

#[global] Hint Unfold pure_State ap_State : CoqMTL.

#[refine]
#[export]
Instance Applicative_State (S : Type) : Applicative (State S) :=
{
    is_functor := Functor_State S;
    pure := @pure_State S;
    ap := @ap_State S
}.
Proof. all: unfold compose; monad. Defined.

(** [State S] is not a commutative applicative because the result of
    the computation depends on the state and changing the argument
    order changes the state in which things are evaluated. *)
Lemma State_not_CommutativeApplicative :
  ~ (forall S : Type, CommutativeApplicative _ (Applicative_State S)).
Proof.
  intro. destruct (H bool). compute in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (fun b => if b then (42, negb b) else (142, b))
    (fun b => if b then (143, b) else (43, negb b))).
  apply (@f_equal _ _ (fun f => f true)) in ap_comm.
  cbn in ap_comm. congruence.
Qed.

(** [State S] is also not [Alternative], because there are no computations
    returning values of the empty type if the state type is nonempty. *)
Lemma State_not_Alternative :
  (forall S : Type, Alternative (State S)) -> False.
Proof.
  unfold State. intro.
  destruct (X unit). destruct (aempty False tt).
  assumption.
Qed.

(** We can can sequence two stateful computation by running the first and
    feeding its result and state into the second. *)
Definition bind_State
  {S A B : Type} (sa : State S A) (f : A -> State S B)
    : State S B := fun s : S => let (a, s') := sa s in f a s'.

#[global] Hint Unfold bind_State : CoqMTL.

#[refine]
#[export]
Instance Monad_State (S : Type) : Monad (State S) :=
{
    is_applicative := Applicative_State S;
    bind := @bind_State S
}.
Proof. all: monad. Defined.

(** [State S] is the primordial example of a state monad. *)
#[refine]
#[export]
Instance MonadState_State
  (S : Type) : MonadState S (State S) (Monad_State S) :=
{
    get := fun s : S => (s, s);
    put := fun s : S => fun _ => (tt, s)
}.
Proof. all: hs. Defined.