From CoqMTL Require Import Control.All.
From CoqMTL Require Import Control.Monad.Trans.
From CoqMTL Require Import Control.Monad.Class.All.

From CoqMTL Require Import Misc.Monoid.

(** A monad transformer that adds a layer of the continuation monad on
    top of the monad stack [M]. *)
Definition ContT (R : Type) (M : Type -> Type) (A : Type)
  : Type := (A -> M R) -> M R.

(** [fmap], [pure], [ap] and [bind] are defined just as for the basic
    [Cont] monad. Note that they don't at all use the fact that [M] is
    a monad. *)

Section ContT_instances.

Variables
  (R : Type)
  (M : Type -> Type)
  (inst : Monad M).

Definition fmap_ContT
  (A B : Type) (f : A -> B) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => y (f a)).

#[refine]
#[export]
Instance FunctorContT : Functor (ContT R M) :=
{
  fmap := fmap_ContT;
}.
Proof. all: reflexivity. Defined.

Definition pure_ContT (A : Type) (x : A) : ContT R M A :=
  fun y : A -> M R => y x.

Definition ap_ContT
  (A B : Type) (mf : ContT R M (A -> B)) (ma : ContT R M A) : ContT R M B :=
    fun y : B -> M R => mf (fun f : A -> B => ma (fun a : A => y (f a))).

#[refine]
#[export]
Instance ApplicativeContT : Applicative (ContT R M) :=
{
  is_functor := FunctorContT;
  pure := pure_ContT;
  ap := ap_ContT;
}.
Proof. all: reflexivity. Defined.

Definition bind_ContT
  (A B : Type) (x : ContT R M A) (f : A -> ContT R M B) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => f a y).

#[refine]
#[export]
Instance Monad_ContT : Monad (ContT R M) :=
{
  is_applicative := ApplicativeContT;
  bind := bind_ContT;
}.
Proof. all: reflexivity. Defined.

(** We can lift a computation into the continuation monad by binding it
    to the continuation. *)
Definition lift_ContT
  (A : Type) (ma : M A) : ContT R M A :=
    fun k : A -> M R => ma >>= k.

End ContT_instances.

#[global] Hint Unfold
  fmap_ContT pure_ContT ap_ContT bind_ContT lift_ContT : CoqMTL.

#[refine]
#[export]
Instance MonadTrans_ContT (R : Type) : MonadTrans (ContT R) :=
{
  is_monad := fun M _ => @Monad_ContT R M;
  lift := @lift_ContT R;
}.
Proof. all: monad. Defined.

(** If we transform a nondeterministic monad, we also get a
    nondeterministic monad. *)

#[refine]
#[export]
Instance MonadAlt_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (ContT R M) (Monad_ContT R M) :=
{
  choose :=
    fun A x y k => choose (x k) (y k);
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadFail_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (ContT R M) (Monad_ContT R M) :=
{
  fail := fun A k => fail;
}.
Proof. reflexivity. Defined.

#[refine]
#[export]
Instance MonadNondet_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (ContT R M) (Monad_ContT R M) :=
{
  instF := @MonadFail_ContT R M inst (@instF _ _ inst');
  instA := @MonadAlt_ContT R M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

(** However, if [M] is an exception monad, we have a problem with the law
    [catch_pure]. Because [pure_ContT] doesn't use [M]'s [pure] in its
    definition, we can't just apply the law [catch_pure] coming from [M]
    and everything breaks. I am not sure whether this is a real problem
    or me not being able to figure it out. *)
#[refine]
#[export]
Instance MonadExcept_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (ContT R M) (Monad_ContT R M) :=
{
  instF := @MonadFail_ContT R M inst inst';
  catch := fun A x y k => catch (x k) (y k);
}.
Proof.
  1-3: monad.
  intros. ext k. cbn. unfold pure_ContT.
Abort.

(** Transforming a reader, writer or state monad also results in such a
    monad. *)

#[refine]
#[export]
Instance MonadReader_ContT
  (E R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (ContT R M) (Monad_ContT R M) :=
{
  ask := fun k => ask >>= k;
}.
Proof.
  hs. ext k. unfold const, id.
  rewrite <- constrA_spec, constrA_bind_assoc, ask_ask. reflexivity.
Defined.

(** This instance is dubious, because [listen] doesn't refer to [M]'s
    [listen]. *)
#[refine]
#[export]
Instance MonadWriter_ContT
  (R : Type) (W : Monoid) (M : Type -> Type)
  (instM : Monad M) (instMW : MonadWriter W M instM)
  : MonadWriter W (ContT R M) (Monad_ContT R M) :=
{
  tell w := fun k => tell w >>= k;
  listen := fun A x k => x (fun a => k (a, neutr));
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadState_ContT
  (S R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (ContT R M) (Monad_ContT R M) :=
{
  get := fun k => get >>= k;
  put := fun s k => put s >> k tt;
}.
Proof.
  all: hs.
  - ext k. hs.
  - ext k. rewrite constrA_spec, <- bind_assoc, put_get'. hs.
  - ext k. rewrite <- bind_constrA_assoc. hs.
  - ext k'. rewrite get_get. reflexivity.
Defined.

(** Even though [ContT] preserves [MonadNondet] and [MonadState], it
    doesn't preserve [MonadStateNondet]. For example, we can't prove
    [seq_fail_r], because the inner monad's [fail] only occurs inside
    the continuation, which doesn't necessarily get called - it can
    be thrown away. *)
#[refine]
#[export]
Instance MonadStateNondet_ContT
  (S R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (ContT R M) (Monad_ContT R M) :=
{
  instS := MonadState_ContT S R M inst inst';
  instN := MonadNondet_ContT R M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn. unfold bind_ContT.
    ext k.
  all: monad.
Abort.

(** If [M] is the free monad of [F], so is [ContT R M]. *)
#[refine]
#[export]
Instance MonadFree_ContT
  (F : Type -> Type) (instF : Functor F)
  (R : Type) (M : Type -> Type)
  (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (ContT R M) instF (Monad_ContT R M) :=
{
  wrap := fun A m k => wrap (fmap (fun x => x k) m);
}.
Proof.
  monad. rewrite <- !fmap_comp'.
  unfold compose. reflexivity.
Defined.