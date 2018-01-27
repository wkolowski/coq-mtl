Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.

Definition Lazy (A : Type) : Type := unit -> A.

Definition delay {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition force {A : Type} (la : Lazy A) : A := la tt.

Definition fmap_Lazy {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
  fun _ => f (la tt).

Instance FunctorLazy : Functor Lazy :=
{
    fmap := @fmap_Lazy;
}.
Proof.
  intro. unfold id, fmap_Lazy. ext la. ext u. destruct u. reflexivity.
  intros. unfold compose, fmap_Lazy. ext la. reflexivity.
Defined.

Definition pure_Lazy {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition ap_Lazy
  {A B : Type} (f : Lazy (A -> B)) (x : Lazy A) : Lazy B :=
    fun _ => f tt (x tt).

Instance ApplicativeLazy : Applicative Lazy :=
{
    is_functor := FunctorLazy;
    pure := @pure_Lazy;
    ap := @ap_Lazy;
}.
Proof.
  all: try reflexivity.
  intros. compute. ext u. destruct u. reflexivity.
Defined.

Definition bind_Lazy
  {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
    f (la tt).

Instance MonadLazy : Monad Lazy :=
{
    is_applicative := ApplicativeLazy;
    bind := @bind_Lazy
}.
Proof.
  all: try reflexivity.
  all: compute; intros.
    ext u. destruct u. reflexivity.
Defined.

Eval lazy in
  delay 5 >>= fun n : nat =>
  delay 2 >>= fun m : nat => delay (n * m).

Eval lazy in
  delay (2 + 2) >>= fun n : nat => delay (2 * n).