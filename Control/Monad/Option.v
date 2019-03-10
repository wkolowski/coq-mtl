Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** A monad that models computations that can fail. *)
Definition Option (A : Type) : Type := option A.

(** We map over a computation by applying the function only if there's a
    result and doing nothing otherwise. *)
Definition fmap_Option
  {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Hint Unfold fmap_Option : HSLib.

(** [Functor] laws can be proven by an easy case analysis, which can be
    handled automatically. *)
Instance Functor_Option : Functor option :=
{
    fmap := @fmap_Option
}.
Proof. all: monad. Defined.

(** The constructor [Some] represents a total computation that has a
    result. *)
Definition pure_Option := @Some.

(** We can apply a partial function to a partial value by running the
    computations and checking if the results are present. If both are
    there, just apply the function to the argument. Otherwise there's
    no result. *)
Definition ap_Option
  {A B : Type} (of : option (A -> B)) (oa : option A) : option B :=
match of, oa with
    | Some f, Some a => Some (f a)
    | _, _ => None
end.

Hint Unfold pure_Option ap_Option : HSLib.

Instance Applicative_Option : Applicative option :=
{
    is_functor := Functor_Option;
    pure := pure_Option;
    ap := @ap_Option
}.
Proof. all: monad. Defined.

(** [None] represents a computation whose value is missing. *)
Definition aempty_Option {A : Type} : option A := None.

(** We can "sum" partial computations by running the first one. If it has
    a result, return it. Otherwise return the second computation. *)
Definition aplus_Option {A : Type} (x y : option A) : option A :=
match x, y with
    | None, y => y
    | Some a, _ => Some a
end.

Hint Unfold aempty_Option aplus_Option : HSLib.

Instance Alternative_Option : Alternative option :=
{
    is_applicative := Applicative_Option;
    aempty := @aempty_Option;
    aplus := @aplus_Option
}.
Proof. all: monad. Defined.

(** To sequence computations, we run both and return a result if both
    succeeded or fail if either of them failed. *)
Definition bind_Option 
  {A B : Type} (oa : option A) (f : A -> option B) : option B :=
match oa with
    | None => None
    | Some a => f a
end.

Hint Unfold bind_Option : HSLib.

(** Failing is commutative, because it doesn't matter what fails nor in
    what order - only the presence of failure is important. *)
Instance CommutativeApplicative_Option :
  CommutativeApplicative _ Applicative_Option.
Proof.
  split. monad.
Defined.

Instance Monad_Option : Monad option :=
{
    is_applicative := Applicative_Option;
    bind := @bind_Option
}.
Proof. all: monad. Defined.

Instance MonadFail_Option : MonadFail option Monad_Option :=
{
    fail := @None;
}.
Proof. intros. compute. reflexivity. Defined.

Definition foldMap_Option
  {A : Type} {M : Monoid} (f : A -> M) (oa : option A) : M :=
match oa with
    | None => neutr
    | Some a => f a
end.

Hint Unfold foldMap_Option : HSLib.

Instance Foldable_Option : Foldable option :=
{
    foldMap := @foldMap_Option
}.
Proof. monad. Defined.