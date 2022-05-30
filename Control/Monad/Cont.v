From CoqMTL Require Import Control.All.

(** A monad that models computations which have access to their control
    context. This makes it possible for them to use complicated control
    constructs, like aborting a computation or throwing an exception. *)
Definition Cont (R A : Type) : Type := (A -> R) -> R.

(** We can map over such computation by composing the function to be
    mapped with the continuation. *)
Definition fmap_Cont
  {R A B : Type} (f : A -> B) (m : Cont R A) : Cont R B :=
    fun g : B -> R => m (f .> g).

#[refine]
#[export]
Instance Functor_Cont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof. all: reflexivity. Defined.

(** We can inject a value into the monad by feeding it into the
    continuation. *)
Definition pure_Cont
  {R A : Type} (a : A) : Cont R A :=
    fun f : A -> R => f a.

Definition ap_Cont
  {R A B : Type} (f : Cont R (A -> B)) (x : Cont R A) : Cont R B :=
    fun kb : B -> R => f (fun ka : A -> B => x (ka .> kb)).

#[refine]
#[export]
Instance Applicative_Cont (R : Type) : Applicative (Cont R) :=
{
    is_functor := Functor_Cont R;
    pure := @pure_Cont R;
    ap := @ap_Cont R
}.
Proof. all: reflexivity. Defined.

(** We can sequence two computations by running the first one with a
    continuation that feeds it to the second one together with the
    continuation. *)
Definition bind_Cont
  {R A B : Type} (x : Cont R A) (f : A -> Cont R B) : Cont R B :=
    fun g : B -> R => x (fun a : A => f a g).

(** It turns out that [Cont] is neither [Alternative] nor commutative.
    It shouldn't surprise us, since it is a "mother of all monads" and
    not all monads have instances of [Alternative] or
    [CommutativeApplicative]. *)

Lemma Cont_not_Alternative :
  (forall R : Type, Alternative (Cont R)) -> False.
Proof.
  unfold Cont. intro. destruct (X False).
  apply aempty with False. trivial.
Qed.

Lemma Cont_not_CommutativeApplicative :
  ~ (forall R : Type, CommutativeApplicative _ (Applicative_Cont R)).
Proof.
  intro. destruct (H bool).
  specialize (ap_comm bool bool _ (fun _ => id) (const true) (const false)).
  compute in ap_comm. apply (f_equal (fun f => f id)) in ap_comm.
  inversion ap_comm.
Qed.

#[refine]
#[export]
Instance Monad_Cont (R : Type) : Monad (Cont R) :=
{
    is_applicative := Applicative_Cont R;
    bind := @bind_Cont R
}.
Proof. all: reflexivity. Defined.

#[global] Hint Unfold fmap_Cont pure_Cont ap_Cont bind_Cont : CoqMTL.

(** For [Cont R], contrary to [Codensity R], we can define both kinds of
    callCC constructively. The second definition is taken from Purescript's
    Pursuit library. *)

Definition callCC
  {R A B : Type} (f : (A -> Cont R B) -> Cont R A) : Cont R A :=
    fun ar : A -> R => f (fun (a : A) (_ : B -> R) => ar a) ar.

Definition callCC'
  {R A : Type} (f : (forall B : Type, A -> Cont R B) -> Cont R A)
  : Cont R A :=
    fun k : A -> R => f (fun (B : Type) (a : A) (_ : B -> R) => k a) k.