Require Import Control.All.

(** An attempt at monad that models a computation that has no side effects,
    but is evaluated lazily. According to my experiments, it doesn't really
    work. *)
Definition Lazy (A : Type) : Type := unit -> A.

Definition delay {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition force {A : Type} (la : Lazy A) : A := la tt.

(** All [Functor], [Applicative] and [Monad] operations are just like
    these for [Identity], but wrapped in [delay] for laziness. *)

Definition fmap_Lazy {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
  delay $ f (la tt).

#[refine]
Instance Functor_Lazy : Functor Lazy :=
{
    fmap := @fmap_Lazy;
}.
Proof. all: monad. Defined.

Definition pure_Lazy {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition ap_Lazy
  {A B : Type} (f : Lazy (A -> B)) (x : Lazy A) : Lazy B :=
    fun _ => f tt (x tt).

#[refine]
Instance Applicative_Lazy : Applicative Lazy :=
{
    is_functor := Functor_Lazy;
    pure := @pure_Lazy;
    ap := @ap_Lazy;
}.
Proof.
  monad.
  all: reflexivity.
Defined.

Definition bind_Lazy
  {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
    fun _ => f (la tt) tt.

#[refine]
Instance Monad_Lazy : Monad Lazy :=
{
    is_applicative := Applicative_Lazy;
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