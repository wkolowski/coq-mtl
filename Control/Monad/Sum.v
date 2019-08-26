Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** A monad which models a computation that can result in an error. *)
Definition Sum (E A : Type) : Type := sum E A.

(** We can map over a computation by applying the function if running
    the computation succeeds and leaving an erroneous result intact. *)
Definition fmap_Sum
  {E A B : Type} (f : A -> B) (x : sum E A) : sum E B :=
match x with
    | inl a => inl a
    | inr b => inr (f b)
end.

Hint Unfold fmap_Sum : CoqMTL.

Instance Functor_Sum (E : Type) : Functor (sum E) :=
{
    fmap := @fmap_Sum E
}.
Proof. all: monad. Defined.

(** A value can be turned into a computation by declaring it to be
    successful. *)
Definition pure_Sum {E A : Type} (x : A) : sum E A := inr x.

(** We can apply a computation producing a function to a computation
    producing an argument by running both and applying the resulting
    function to the argument. If either of the computations results
    in an error, return the first encountered error. *)
Definition ap_Sum
  {E A B : Type} (sf : sum E (A -> B)) (sa : sum E A) : sum E B :=
match sf, sa with
    | inl a, _ => inl a
    | _, inl a => inl a
    | inr f, inr x => inr (f x)
end.

Hint Unfold pure_Sum ap_Sum : CoqMTL.

Instance Applicative_Sum (E : Type) : Applicative (sum E) :=
{
    is_functor := Functor_Sum E;
    pure := @pure_Sum E;
    ap := @ap_Sum E
}.
Proof. all: monad. Defined.

(** Computations that can fail are neither a [CommutativeApplicative] nor
    an [Alternative], because the order of errors matter - for example,
    different error messages mean different errors. *)

Lemma Sum_not_CommutativeApplicative :
  ~ (forall E : Type, CommutativeApplicative _ (Applicative_Sum E)).
Proof.
  intro. destruct (H bool).
  specialize (ap_comm nat nat nat (fun _ => id) (inl true) (inl false)).
  compute in ap_comm. congruence.
Qed.

Lemma Sum_not_alternative :
  (forall E : Type, Alternative (sum E)) -> False.
Proof.
  intro inst. destruct (inst False).
  destruct (aempty False); assumption. 
Qed.

(** If a computation doesn't fail, we may feed it to a function which
    produces another such computation. *)
Definition bind_Sum
  {E A B : Type} (sa : sum E A) (f : A -> sum E B) : sum E B :=
match sa with
    | inl e => inl e
    | inr a => f a
end.

Hint Unfold bind_Sum : CoqMTL.

Instance Monad_Sum (A : Type) : Monad (sum A) :=
{
    is_applicative := Applicative_Sum A;
    bind := @bind_Sum A
}.
Proof. all: monad. Defined.

(** [sum] supports failure only if the error type is inhabited. *)

Definition fail_Sum {E : Type} (e : E) {A : Type} : Sum E A := inl e.

Instance MonadFail_Sum
  (E : Type) (e : E)
  : MonadFail (Sum E) (Monad_Sum E) :=
{
    fail := @fail_Sum E e
}.
Proof. reflexivity. Defined.

Instance MonadExcept_Sum
  (E : Type) (e : E) : MonadExcept (sum E) (Monad_Sum E) :=
{
    instF := MonadFail_Sum E e;
    catch :=
      fun A x y =>
        match x with
            | inl e => y
            | inr a => inr a
        end

}.
Proof.
  all: monad. unfold fail_Sum.
Abort.

Definition foldMap_Sum
  {E A : Type} {M : Monoid} (f : A -> M) (x : sum E A) : M :=
match x with
    | inl _ => neutr
    | inr a => f a
end.

Hint Unfold foldMap_Sum : CoqMTL.

Instance FoldableSum (E : Type) : Foldable (sum E) :=
{
    foldMap := @foldMap_Sum E
}.
Proof. monad. Defined.