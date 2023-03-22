From CoqMTL Require Import Control.

(** This module contains proofs that various definitions of monads are
    equivalent. More precisely, we prove that these definitions are
    equivalent in the sense of the ability to construct  an instance of
    each of them from the other:
    - the main definition used throughout the library (from Control.Monad),
      which says that a monad is an [Applicative] functor with [bind],
      satisfying the laws [bind_pure_l], [bind_pure_r], [bind_assoc] and
      [bind_ap], which relates the [Applicative] and [Monad] structure

    - the join-based definition (from Theory.Equivs.MonadJoin), which says
      that a monad is an [Applicative] functor with [join] that satisfies
      the laws [join_fmap_join], [join_pure], [join_fmap_pure],
      [join_fmap_fmap] and [join_ap]
    - the Kleisli Triple definition, which is very similar to that of
      Theory.Equivs.MonadBind, but has different operation names and
      some arguments flipped

    As of now, I can't prove that these are equivalent to the compM-based
    definition (from Theory.Equivs.MonadComp), which says that a monad is
    something that has monadic composition which is associative and has
    a neutral element. *)

(** First we require all the necessary modules and repack them so as to
    refer to them by nonconflicting names. *)

From CoqMTL Require MonadJoin.
From CoqMTL Require MonadBind.
From CoqMTL Require MonadComp.

Module Join.
Include MonadJoin.
End Join.

Module Bind.
Include MonadBind.
End Bind.

Module Comp.
Include MonadComp.
End Comp.

(** Each proof consists of two instances, one deriving [Monad] from the
    definition at hand and the other one deriving an instance for that
    definition from [Monad]. *)

(** * join-based definition *)

#[refine]
#[export]
Instance Join_to_Monad
  (M : Type -> Type) (inst : Join.Monad M) : Monad M :=
{
  is_applicative := @Join.is_applicative M inst;
  bind := @Join.bind M inst
}.
Proof.
  1, 2, 4: MonadJoin.mjoin.
  apply Join.assoc.
Defined.

#[refine]
#[export]
Instance Monad_to_Join (M : Type -> Type) (inst : Monad M)
  : Join.Monad M :=
{
  is_applicative := @is_applicative M inst;
  join := @join M inst
}.
Proof.
  all: intros; unfold join, compose; try ext x.
    rewrite bind_assoc, bind_fmap. unfold compose, id. reflexivity.
    rewrite bind_pure_l. reflexivity.
    rewrite bind_fmap, <- bind_pure_r. f_equal.
    rewrite bind_fmap, fmap_bind. f_equal.
    rewrite !bind_ap. monad.
Defined.

(** * bind-based definition *)

#[refine]
#[export]
Instance MonadBind_to_Monad
  (M : Type -> Type) (inst : Bind.Monad M) : Monad M :=
{
  is_applicative := @MonadBind.Applicative_MonadBind M inst;
  bind := @MonadBind.bind M inst;
}.
Proof. all: MonadBind.mbind. Defined.

#[refine]
#[export]
Instance Monad_to_MonadBind
  (M : Type -> Type) (inst : Monad M) : MonadBind.Monad M :=
{
  pure := @pure M inst;
  bind := @bind M inst;
}.
Proof. all: monad. Defined.

(** * Kleisli triple *)

From CoqMTL Require Import KleisliTriple.

#[refine]
#[export]
Instance Monad_to_KleisliTriple
  (M : Type -> Type) (inst : Monad M) : KleisliTriple M :=
{
  eta := @pure M inst;
  star := fun A B => flip (@bind M inst A B);
}.
Proof.
  all: unfold flip; monad.
Defined.

#[refine]
#[export]
Instance KleisliTriple_to_Monad
  (M : Type -> Type) (inst : KleisliTriple M) : Monad M :=
{
  is_applicative := Applicative_Kleisli M inst;
  bind := @bind_Kleisli M inst;
}.
Proof. all: kleisli. Defined.

(** * compM-based definition *)

#[refine]
#[export]
Instance Monad_to_MonadComp
  (M : Type -> Type) (inst : Monad M) : MonadComp.Monad M :=
{
  is_applicative := is_applicative;
  compM := @compM M inst;
}.
Proof. all: unfold compM; monad. Defined.

(** TODO: MonadComp_to_Monad *)