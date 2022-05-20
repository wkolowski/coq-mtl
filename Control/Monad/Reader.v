Require Import Control.All.
Require Import Control.Monad.Class.All.

(** A monad which represents a computation that has access to an immutable,
    read-only environment (a single cell of memory of type [R]). *)
Definition Reader (R A : Type) : Type := R -> A.

(** We can map over a computation by providing it with an environment and
    then applying the function. *)
Definition fmap_Reader
  {R A B : Type} (f : A -> B) (x : Reader R A) : Reader R B :=
    fun r : R => f (x r).

#[refine]
#[export]
Instance Functor_Reader (R : Type) : Functor (Reader R) :=
{
    fmap := @fmap_Reader R
}.
Proof. all: reflexivity. Defined.

(** We can inject a value into the monad by just ignoring the environment. *)
Definition pure_Reader
  {R A : Type} (a : A) : Reader R A :=
    fun _ : R => a.

(** We can apply a monadic function to a monadic argument by reading the
    environment once and using it to run both computations. Then we can
    apply the resulting function to the resulting argument. *)
Definition ap_Reader
  {R A B : Type} (f : Reader R (A -> B)) (x : Reader R A) : Reader R B :=
    fun r : R => f r (x r).

#[refine]
#[export]
Instance ApplicativeReader (R : Type) : Applicative (Reader R) :=
{
    is_functor := Functor_Reader R;
    pure := @pure_Reader R;
    ap := @ap_Reader R
}.
Proof. all: reflexivity. Defined.

(** The order of reading the environments doesn't matter, so it can be
    freely permuted. Therefore [Reader R] is a commutative applicative
    functor. *)
#[export]
Instance CommutativeApplicative_Reader (R : Type) :
  CommutativeApplicative _ (ApplicativeReader R).
Proof. split. reflexivity. Defined.

(** [Reader R] is not [Alternative], because we can't produce a value
    of the empty type unless the type of environment is also empty. *)
Lemma Reader_not_Alternative :
  (forall R : Type, Alternative (Reader R)) -> False.
Proof.
  intro. destruct (X True).
  apply (aempty False). trivial.
Qed.

(** We can sequence two computations by reading the environment, using
    it to run the argument and then feeding the result to the function
    and using the environment to run it. *)
Definition bind_Reader
  {R A B : Type} (x : Reader R A) (f : A -> Reader R B) : Reader R B :=
    fun r : R => f (x r) r.

#[refine]
#[export]
Instance Monad_Reader (R : Type) : Monad (Reader R) :=
{
    is_applicative := ApplicativeReader R;
    bind := @bind_Reader R
}.
Proof. all: reflexivity. Defined.

(** [Reader R] is the primordial [MonadReader] instance. [ask] is just
    the identity. *)
#[refine]
#[export]
Instance MonadReader_Reader
  (R : Type) : MonadReader R (Reader R) (Monad_Reader R) :=
{
    ask := id
}.
Proof. reflexivity. Defined.

#[global] Hint Unfold fmap_Reader pure_Reader ap_Reader bind_Reader : CoqMTL.