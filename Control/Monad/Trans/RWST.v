Require Import Control.

Require Import HSLib.Control.Monad.Identity.

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

Definition lift_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A : Type}
  (x : M A) : RWST W R S M A :=
    fun r s =>
      x >>= fun a : A => pure (a, s, neutr).

Hint Unfold lift_RWST : HSLib.

Instance MonadTrans_RWST
  {W : Monoid} {R S : Type} : MonadTrans (RWST W R S) :=
{
    lift := @lift_RWST W R S
}.
Proof. all: unfold compose; monad. Defined.

Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

Instance MonadReader_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadReader R (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    ask := fun r s => pure (r, s, neutr);
}.
Proof. monad. Defined.

Instance MonadState_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadState S (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    get := fun _ (s : S) => pure (s, s, neutr);
    put := fun s : S => fun _ _ => pure (tt, s, neutr);
}.
Proof.
  1-3: monad.
  intros. ext r. ext s. cbn. monad.
Defined.

Require Import Control.Monad.Class.All.

Instance MonadAlt_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    choose :=
      fun A x y => fun r s => choose (x r s) (y r s )
}.
Proof.
  intros. ext r. ext s. rewrite choose_assoc. reflexivity.
  intros. ext r. ext s. cbn. unfold bind_RWST. apply choose_bind_l.
Defined.

Instance MonadFail_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    fail := fun A _ _ => @fail M inst inst' (A * S * W)
}.
Proof.
  intros. ext r. ext s. cbn. unfold bind_RWST.
  rewrite bind_fail_l. reflexivity.
Defined.

Instance MonadNondet_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instF := @MonadFail_RWST W R S M inst (@instF _ _ inst');
    instA := @MonadAlt_RWST W R S M inst (@instA _ _ inst');
}.
Proof.
  intros. cbn. ext r. ext s. rewrite choose_fail_l. reflexivity.
  intros. cbn. ext r. ext s. rewrite choose_fail_r. reflexivity.
Defined.

Instance MonadExcept_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instF := @MonadFail_RWST W R S M inst inst';
    catch :=
      fun A x y => fun r s => catch (x r s) (y r s);
}.
Proof.
  all: cbn; intros; ext r; ext s.
    apply catch_fail_l.
    apply catch_fail_r.
    apply catch_assoc.
    unfold pure_RWST. apply catch_pure.
Defined.

Instance MonadStateNondet_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instS := MonadState_RWST W R S M inst;
    instN := MonadNondet_RWST W R S M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn.
    unfold bind_RWST. ext r. ext s.
    replace (fun _ => _)
       with (fun _ : A * S * W => @fail M inst inst' (B * S * W)).
      rewrite <- constrA_spec. apply seq_fail_r.
      ext asw. destruct asw as [[_ _] w]. rewrite bind_fail_l. reflexivity.
  intros. cbn. unfold bind_RWST. ext r. ext s.
    rewrite <- bind_choose_distr. f_equal.
    ext asw. destruct asw as [[a sa] wa]. apply choose_bind_l.
Defined.

(*
Instance MonadFree_RWST
  (R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFree S M inst)
  : MonadFree S (RWST R M) (Monad_RWST R M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  intros. ext k. cbn. unfold fmap_RWST, const, id.
    rewrite <- constrA_assoc. rewrite put_put. reflexivity.
  Focus 3.
  intros A f. ext k. cbn. unfold bind_RWST, pure_RWST.
    rewrite get_get. reflexivity.
Abort.
*)