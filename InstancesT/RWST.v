Require Import Control.

Require Import HSLib.Instances.Identity.

Definition RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (A : Type) : Type :=
    R -> S -> M (A * S * W)%type.

Definition fmap_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : A -> B) (x : RWST W R S M A) : RWST W R S M B :=
    fun r s =>
      x r s >>= fun '(x', sx, wx) => pure $ (f x', sx, wx).
(*    fun r s => do
      (x', sx, wx) <<-- x r s;;;
      pure $ (f x', sx, wx).
*)
Hint Unfold RWST fmap_RWST : HSLib.

Instance Functor_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
    : Functor (RWST W R S M) :=
{
    fmap := @fmap_RWST W R S M inst
}.
Proof. all: unfold compose; monad. Defined.

Definition pure_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A : Type}
  (x : A) : RWST W R S M A :=
    fun _ s => pure (x, s, neutr).

Definition ap_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : RWST W R S M (A -> B)) (x : RWST W R S M A) : RWST W R S M B :=
    fun r s =>
      f r s >>= fun '(f', sf, wf) =>
      x r sf >>= fun '(x', sx, wx) => pure (f' x', sx, op wf wx). (*
      let '(x', sx, wx) := x r s in
      let '(f', sf, wf) := f r sx in (f' x', sf, op wx wf). *)

Hint Unfold pure_RWST ap_RWST : HSLib.

Instance Applicative_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
    : Applicative (RWST W R S M) :=
{
    is_functor := Functor_RWST W R S M inst;
    pure := @pure_RWST W R S M inst;
    ap := @ap_RWST W R S M inst;
}.
Proof. all: monad. Defined.

Theorem RWST_not_CommutativeApplicative :
  ~ (forall (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M),
      CommutativeApplicative _ (Applicative_RWST W R S M inst)).
Proof.
  intro. destruct (H (Monoid_list_app bool) unit unit Identity _).
  unfold RWST in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (fun _ _ => (42, tt, [true; false]))
    (fun _ _ => (43, tt, [false; true]))).
  compute in ap_comm. do 2 apply (f_equal (fun f => f tt)) in ap_comm.
  inv ap_comm.
Qed.

Theorem RWST_not_Alternative :
  (forall (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (RWST W R S M)) -> False.
Proof.
  intro H. destruct (H Monoid_unit unit unit Identity _).
  clear - aempty. compute in aempty.
  destruct (aempty False tt tt) as [[f _] _].
  assumption.
Qed.

Definition bind_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : RWST W R S M A) (f : A -> RWST W R S M B) : RWST W R S M B :=
    fun r s =>
      x r s >>= fun '(x', sx, wx) =>
      f x' r sx >>= fun '(b, sb, wb) => pure (b, sb, op wx wb).

Hint Unfold bind_RWST : HSLib.

Instance Monad_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
    : Monad (RWST W R S M) :=
{
    is_applicative := Applicative_RWST W R S M inst;
    bind := @bind_RWST W R S M inst
}.
Proof. all: monad. Defined.