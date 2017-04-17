Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import Applicative.
Require Import HSLib.MonadJoin.Monad.

Print Monad.

Definition Reader (R A : Type) : Type := R -> A.

Print Functor.

Definition fmap_Reader {R A B : Type} (f : A -> B)
    (ra : Reader R A) : Reader R B :=
    fun r : R => f (ra r).

Instance FunctorReader (R : Type) : Functor (Reader R) :=
{
    fmap := @fmap_Reader R
}.
Proof.
  intros. extensionality ra. extensionality r. unfold fmap_Reader, id. trivial.
  intros. extensionality ra. extensionality r. unfold fmap_Reader, id, compose.
    trivial.
Defined.
Print Applicative.

Definition ret_Reader {R A : Type} (a : A) : Reader R A :=
    fun _ : R => a.

Definition ap_Reader {R A B : Type} (f : Reader R (A -> B)) (ra : Reader R A)
    : Reader R B := fun r : R => f r (ra r).

Instance ApplicativeReader (R : Type) : Applicative (Reader R) :=
{
    is_functor := FunctorReader R;
    ret := @ret_Reader R;
    ap := @ap_Reader R
}.
Proof.
  trivial.
  trivial.
  trivial.
  trivial.
Defined.

Definition join_Reader {R A : Type} (rra : Reader R (Reader R A))
    : Reader R A := fun r : R => rra r r.

Instance MonadReader (R : Type) : Monad (Reader R) :=
{
    ret := @ret_Reader R;
    join := @join_Reader R
}.
Proof.
  trivial.
  trivial.
Defined.