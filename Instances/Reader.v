Require Import Control.

Definition Reader (R A : Type) : Type := R -> A.

Definition fmap_Reader
  {R A B : Type} (f : A -> B) (ra : Reader R A) : Reader R B :=
    fun r : R => f (ra r).

Instance FunctorReader (R : Type) : Functor (Reader R) :=
{
    fmap := @fmap_Reader R
}.
Proof. all: hs. Defined.

Definition pure_Reader
  {R A : Type} (a : A) : Reader R A :=
    fun _ : R => a.

Definition ap_Reader
  {R A B : Type} (f : Reader R (A -> B)) (ra : Reader R A) : Reader R B :=
    fun r : R => f r (ra r).

Instance ApplicativeReader (R : Type) : Applicative (Reader R) :=
{
    is_functor := FunctorReader R;
    pure := @pure_Reader R;
    ap := @ap_Reader R
}.
Proof. all: hs. Defined.

Instance CommutativeApplicative_Reader (R : Type) :
  CommutativeApplicative _ (ApplicativeReader R) := {}.
Proof. reflexivity. Qed.

Definition bind_Reader
  {R A B : Type} (ra : Reader R A) (f : A -> Reader R B) : Reader R B :=
    fun r : R => f (ra r) r.

Instance Monad_Reader (R : Type) : Monad (Reader R) :=
{
    is_applicative := ApplicativeReader R;
    bind := @bind_Reader R
}.
Proof. all: hs. Defined.

Hint Unfold Reader fmap_Reader pure_Reader ap_Reader bind_Reader : HSLib.

Require Import MonadClass.All.

Print MonadReader.

Instance MonadReader_Reader
  (R : Type) : MonadReader R (Reader R) (Monad_Reader R) :=
{
    ask := id
}.
Proof. compute. reflexivity. Defined.