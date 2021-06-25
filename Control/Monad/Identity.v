Require Import Control.All.

(** The Identity monad, mainly for use with monad transformers. It models
    the trivial effect, or rather, a lack of any computation effect
    whatsoever. *)
Definition Identity (A : Type) : Type := A.

(** We can map over a computation by applying the function. *)
Definition fmap_Identity
  {A B : Type} (f : A -> B) (a : Identity A) : Identity B := f a.

#[refine]
Instance FunctorIdentity : Functor Identity :=
{
    fmap := @fmap_Identity
}.
Proof. all: reflexivity. Defined.

(** The injection of a value into the monad is just the identity function. *)
Definition pure_Identity {A : Type} (x : A) : Identity A := x.

(** [ap] is the same as [fmap] - it's just the ordinary application. *)
Definition ap_Identity
  {A B : Type} (f : Identity (A -> B)) (x : Identity A) : Identity B := f x.

#[refine]
Instance Applicative_Identity : Applicative Identity :=
{
    is_functor := FunctorIdentity;
    pure := @pure_Identity;
    ap := @ap_Identity
}.
Proof. all: reflexivity. Defined.

(** [bind] is also just function application. *)
Definition bind_Identity
  {A B : Type} (a : Identity A) (f : A -> Identity B) : Identity B := f a.

(** [Identity] is not [Alternative], because we can't a produce a [False]
    out of nowhere. *)
Lemma Identity_not_Alternative :
  Alternative Identity -> False.
Proof.
  destruct 1. apply aempty.
Qed.

(** Since [Identity] has no side effects, it is commutative. *)
Instance CommutativeApplicative_Identity :
  CommutativeApplicative _ Applicative_Identity.
Proof. split. reflexivity. Defined.

#[refine]
Instance Monad_Identity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    bind := @bind_Identity
}.
Proof. all: reflexivity. Defined.

Global Hint Unfold fmap_Identity pure_Identity ap_Identity bind_Identity : CoqMTL.