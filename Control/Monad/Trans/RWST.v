Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.
Require Import Control.Monad.Identity.

Require Import Misc.Monoid.

(** A transformer which to any base monad [M] adds a layer that can read
    the environment, perform logging and read a single cell of state. *)
Definition RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (A : Type) : Type :=
    R -> S -> M (A * S * W)%type.

(** Definitions of [fmap], [pure], [ap], [bind] and so on are made up of
    three parts: to understand each of them, look it up in [ReaderT],
    [WriterT], [StateT]. *)

Definition fmap_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : A -> B) (x : RWST W R S M A) : RWST W R S M B :=
    fun r s =>
      x r s >>= fun '(x', sx, wx) => pure $ (f x', sx, wx).

#[global] Hint Unfold RWST fmap_RWST : CoqMTL.

#[refine]
#[export]
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
      x r sf >>= fun '(x', sx, wx) => pure (f' x', sx, op wf wx).

#[global] Hint Unfold pure_RWST ap_RWST : CoqMTL.

#[refine]
#[export]
Instance Applicative_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
    : Applicative (RWST W R S M) :=
{
    is_functor := Functor_RWST W R S M inst;
    pure := @pure_RWST W R S M inst;
    ap := @ap_RWST W R S M inst;
}.
Proof. all: monad. Defined.

Lemma RWST_not_CommutativeApplicative :
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

Lemma RWST_not_Alternative :
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

#[global] Hint Unfold bind_RWST : CoqMTL.

#[refine]
#[export]
Instance Monad_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
    : Monad (RWST W R S M) :=
{
    is_applicative := Applicative_RWST W R S M inst;
    bind := @bind_RWST W R S M inst
}.
Proof. all: monad. Defined.

(** To lift a computation into the monad, we bind it to a function which
    puts its value next to the current state. It doesn't read the
    environment or write the to the log. *)
Definition lift_RWST
  {W : Monoid} {R S : Type} {M : Type -> Type} {inst : Monad M} {A : Type}
  (x : M A) : RWST W R S M A :=
    fun r s =>
      x >>= fun a : A => pure (a, s, neutr).

#[global] Hint Unfold lift_RWST : CoqMTL.

#[refine]
#[export]
Instance MonadTrans_RWST
  {W : Monoid} {R S : Type} : MonadTrans (RWST W R S) :=
{
    lift := @lift_RWST W R S
}.
Proof. all: unfold compose; monad. Defined.

(** [RWST] puts a layer of [MonadReader], [MonadWriter] and [MonadState]
    on top of the base monad [M]. *)

#[refine]
#[export]
Instance MonadReader_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadReader R (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    ask := fun r s => pure (r, s, neutr);
}.
Proof. monad. Defined.

#[refine]
#[export]
Instance MonadWriter_RWST
  (R S : Type) (W : Monoid) (M : Type -> Type) (inst : Monad M)
  : MonadWriter W (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    tell := fun w => fun _ s => pure (tt, s, w);
    listen :=
      fun A (m : R -> S -> M (A * S * W)%type) =>
        fun r s =>
          m r s >>= fun '(a, s, w) => pure (a, w, s, neutr);
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadState_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadState S (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    get := fun _ (s : S) => pure (s, s, neutr);
    put := fun s : S => fun _ _ => pure (tt, s, neutr);
}.
Proof.
  1-3: monad.
  intros. cbn. ext r. ext s. monad.
Defined.

(** Just like [ReaderT], [WriterT] and [StateT], [RWST] preserves all other
    kinds of monads. *)

#[refine]
#[export]
Instance MonadAlt_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    choose :=
      fun A x y => fun r s => choose (x r s) (y r s )
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadFail_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    fail := fun A _ _ => @fail M inst inst' (A * S * W)
}.
Proof. monad. Defined.

#[refine]
#[export]
Instance MonadNondet_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instF := @MonadFail_RWST W R S M inst (@instF _ _ inst');
    instA := @MonadAlt_RWST W R S M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadStateNondet_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instS := MonadState_RWST W R S M inst;
    instN := MonadNondet_RWST W R S M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn. hs. ext2 r s.
    rewrite <- (seq_fail_r _ _ (x r s)) at 1.
    rewrite constrA_spec. f_equal. ext y.
    destruct y as [[a s'] w]. apply bind_fail_l.
  intros. cbn. unfold bind_RWST. ext r. ext s.
    rewrite <- bind_choose_r. f_equal.
    ext asw. destruct asw as [[a sa] wa]. apply bind_choose_l.
Defined.

#[refine]
#[export]
Instance MonadExcept_RWST
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (RWST W R S M) (Monad_RWST W R S M inst) :=
{
    instF := @MonadFail_RWST W R S M inst inst';
    catch :=
      fun A x y => fun r s => catch (x r s) (y r s);
}.
Proof. all: monad. Defined.

(** If [M] is the free monad of [F], so is [RWST W R S M]. *)
#[refine]
#[export]
Instance MonadFree_RWST
  (F : Type -> Type) (instF : Functor F)
  (W : Monoid) (R S : Type) (M : Type -> Type)
  (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (RWST W R S M) instF (Monad_RWST W R S M instM) :=
{
    wrap :=
      fun A m r s => wrap (fmap (fun x => x r s) m)
}.
Proof.
  intros. ext2 r s. cbn.
  unfold bind_RWST, pure_RWST, RWST in *.
  rewrite <- !fmap_comp'. unfold compose.
  rewrite wrap_law.
  rewrite (wrap_law _ _ (fun a : A => pure (a, s, neutr)) x).
  monad.
Defined.