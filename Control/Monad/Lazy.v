Require Import Control.All.

(** An attempt at a laziness monad. According to my experiments, it doesn't
    really work. *)
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
Proof. all: monad. Defined.

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
  1-5: try reflexivity.
  monad.
Defined.

Definition bind_Lazy
  {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
    fun _ => f (la tt) tt.

Instance MonadLazy : Monad Lazy :=
{
    is_applicative := ApplicativeLazy;
    bind := @bind_Lazy
}.
Proof. all: monad. Defined.

(** Running these computations gives the following times:
    - [cbn] takes ~9.1 seconds for both [repeat 42 10000] and
      [delay $ repeat 42 10000]
    - [lazy] takes ~1.3 seconds in both cases
*)
(*
Time Eval cbn in repeat 42 10000.
Time Eval lazy in repeat 42 10000.
Time Eval lazy in delay $ repeat 42 10000.
Time Eval cbn in delay $ repeat 42 10000.
*)