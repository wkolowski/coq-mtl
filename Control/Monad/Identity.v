Require Import Control.All.

(** The Identity monad, mainly for use with monad transformers. *)
Definition Identity (A : Type) : Type := A.

Definition fmap_Identity
  {A B : Type} (f : A -> B) (a : Identity A) : Identity B := f a.

Instance FunctorIdentity : Functor Identity :=
{
    fmap := @fmap_Identity
}.
Proof. all: reflexivity. Defined.

Definition pure_Identity {A : Type} (x : A) : Identity A := x.

Definition ap_Identity
  {A B : Type} (f : Identity A -> Identity B) (x : Identity A)
    : Identity B := f x.

Instance Applicative_Identity : Applicative Identity :=
{
    is_functor := FunctorIdentity;
    pure := @pure_Identity;
    ap := @ap_Identity
}.
Proof. all: reflexivity. Defined.

Definition bind_Identity
  {A B : Type} (a : Identity A) (f : A -> Identity B) : Identity B := f a.

Lemma Identity_not_Alternative :
  Alternative Identity -> False.
Proof.
  destruct 1. apply aempty.
Qed.

Instance CommutativeApplicative_Identity :
  CommutativeApplicative _ Applicative_Identity.
Proof. split. reflexivity. Defined.

Instance MonadIdentity : Monad Identity :=
{
    is_applicative := Applicative_Identity;
    bind := @bind_Identity
}.
Proof. all: reflexivity. Defined.

Hint Unfold fmap_Identity pure_Identity ap_Identity bind_Identity : HSLib.