Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** [RWS W R S] is a monad which models a computation that can access
    a read-only environment, a write-only log and a single cell of
    read-write memory.

    Note that, somewhat contrary to the name, the order of arguments
    is first the log type [W], then the environment type [R] and finally
    the state type [S]. *)
Definition RWS (W : Monoid) (R S A : Type) : Type :=
  R -> S -> A * S * W.

(** We can map over such a computation by running it and applying a function
    to the result while passing along the state and log it produced. *)
Definition fmap_RWS
  {W : Monoid} {R S A B : Type}
  (f : A -> B) (m : RWS W R S A) : RWS W R S B :=
    fun r s =>
      let
        '(a, s', w) := m r s
      in
        (f a, s', w).

Global Hint Unfold fmap_RWS : CoqMTL.

#[refine]
Instance Functor_RWS (W : Monoid) (R S : Type) : Functor (RWS W R S) :=
{
    fmap := @fmap_RWS W R S
}.
Proof. all: unfold compose; monad. Defined.

(** We can inject a value into this monad without touching the state or
    writing to the log. *)
Definition pure_RWS {W : Monoid} {R S A : Type} (x : A) : RWS W R S A :=
  fun _ s => (x, s, neutr).

(** We can apply a computation to another computation by running them in
    order, applying the result function to the argument, passing along
    the state of the argument and concatenating the logs. *)
Definition ap_RWS
  {W : Monoid} {R S A B : Type}
  (mf : RWS W R S (A -> B)) (mx : RWS W R S A) : RWS W R S B :=
    fun r s => 
      let '(f, sf, wf) := mf r s in
      let '(x, sx, wx) := mx r sf in (f x, sx, op wf wx).

Global Hint Unfold pure_RWS ap_RWS : CoqMTL.

#[refine]
Instance Applicative_RWS
  (W : Monoid) (R S : Type) : Applicative (RWS W R S) :=
{
    is_functor := Functor_RWS W R S;
    pure := @pure_RWS W R S;
    ap := @ap_RWS W R S;
}.
Proof. all: monad. Defined.

(** [Reader] and [Writer] have a commutative [ap], but [State] does not,
    so neither does [RWS]. *)
Lemma RWS_not_CommutativeApplicative :
  ~ (forall (W : Monoid) (R S : Type),
      CommutativeApplicative _ (Applicative_RWS W R S)).
Proof.
  intro. destruct (H (Monoid_list_app bool) unit unit).
  unfold RWS in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (fun _ _ => (42, tt, [true; false]))
    (fun _ _ => (43, tt, [false; true]))).
  compute in ap_comm. do 2 apply (f_equal (fun f => f tt)) in ap_comm.
  inv ap_comm.
Qed.

(** None of its components is [Alternative], so [RWS] is neither. *)
Lemma RWS_not_Alternative :
  forall (W : Monoid) (R S : Type),
    R -> S -> Alternative (RWS W R S) -> False.
Proof.
  destruct 3. destruct (aempty False) as [[f _] _]; assumption. 
Qed.

(** We can sequence two computations by running them in order,
    applying the function to the argument, passing along the
    state of the argument and concatenating the logs. *)
Definition bind_RWS
  {W : Monoid} {R S A B : Type}
  (mx : RWS W R S A) (mf : A -> RWS W R S B) : RWS W R S B :=
    fun r s =>
      let '(x, sx, wx) := mx r s in
      let '(b, sb, wb) := mf x r sx in (b, sb, op wx wb).

Global Hint Unfold bind_RWS : CoqMTL.

#[refine]
Instance Monad_RWS
  (W : Monoid) (R S : Type) : Monad (RWS W R S) :=
{
    is_applicative := Applicative_RWS W R S;
    bind := @bind_RWS W R S
}.
Proof. all: monad. Defined.

(** [RWS W R S] has instances corresponding to all three of its effects. *)

#[refine]
Instance MonadReader_RWS
  (W : Monoid) (R S : Type)
  : MonadReader R (RWS W R S) (Monad_RWS W R S) :=
{
    ask := fun r s => (r, s, neutr);
}.
Proof. hs. Defined.

#[refine]
Instance MonadWriter_RWS
  (W : Monoid) (R S : Type) : MonadWriter W (RWS W R S) (Monad_RWS W R S) :=
{
    tell := fun w => fun r s => (tt, s, w);
    listen :=
      fun A m => fun r s =>
        let '(a, s, w) := m r s in (a, w, s, neutr);
}.
Proof. all: hs; monad. Defined.

#[refine]
Instance MonadState_RWS
  (W : Monoid) (R S : Type) : MonadState S (RWS W R S) (Monad_RWS W R S) :=
{
    get := fun _ (s : S) => (s, s, neutr);
    put := fun s : S => fun _ _ => (tt, s, neutr)
}.
Proof. all: monad. Defined.