Require Import Control.All.

(** The continuation monad. *)
Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition fmap_Cont
  {R A B : Type} (f : A -> B) (ca : Cont R A) : Cont R B :=
    fun g : B -> R => ca (f .> g).

Instance FunctorCont (R : Type) : Functor (Cont R) :=
{
    fmap := @fmap_Cont R
}.
Proof. all: reflexivity. Defined.

Definition pure_Cont
  {R A : Type} (a : A) : Cont R A :=
    fun f : A -> R => f a.

Definition ap_Cont
  {R A B : Type} (f : Cont R (A -> B)) (x : Cont R A) : Cont R B :=
    fun y : B -> R => f (fun h : A -> B => x (fun a : A => y (h a))).

Instance ApplicativeCont (R : Type) : Applicative (Cont R) :=
{
    is_functor := FunctorCont R;
    pure := @pure_Cont R;
    ap := @ap_Cont R
}.
Proof. all: reflexivity. Defined.

Definition bind_Cont
  {R A B : Type} (ca : Cont R A) (f : A -> Cont R B) : Cont R B :=
    fun g : B -> R => ca (fun x : A => f x g).

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
  ~ (forall R : Type, CommutativeApplicative _ (ApplicativeCont R)).
Proof.
  intro. destruct (H bool).
  specialize (ap_comm bool bool _ (fun _ => id) (const true) (const false)).
  compute in ap_comm. apply (f_equal (fun f => f id)) in ap_comm.
  inversion ap_comm.
Qed.

Instance MonadCont (R : Type) : Monad (Cont R) :=
{
    is_applicative := ApplicativeCont R;
    bind := @bind_Cont R
}.
Proof. all: reflexivity. Defined.

Hint Unfold fmap_Cont pure_Cont ap_Cont bind_Cont : HSLib.

Definition callCC
  {R A B : Type} (f : (A -> Cont R B) -> Cont R A) : Cont R A :=
    fun ar : A -> R => f (fun (a : A) (_ : B -> R) => ar a) ar.

(** The type of this one is taken from Purescript's Pursuit library. *)
Definition callCC'
  {R A : Type} (f : (forall B : Type, A -> Cont R B) -> Cont R A)
  : Cont R A :=
    fun k : A -> R => f (fun (B : Type) (a : A) (_ : B -> R) => k a) k.