From CoqMTL Require Import Control.All.
From CoqMTL Require Import Control.Monad.Trans.
From CoqMTL Require Import Control.Monad.Class.All.
From CoqMTL Require Import Control.Monad.Identity.

(** A transformer which puts a layer of the free monad for the functor [F]
    on top of the monad [M]. It is implemented using Church encoding. *)
Definition FreeT (F : Type -> Type) (M : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> M X) -> (F (M X) -> M X) -> M X.

(** To understand a definition of a function, you just have to look at the
    types. Intuition is harder, however. *)

Section FreeT.

Variables
  (F : Type -> Type)
  (M : Type -> Type)
  (inst : Monad M).

Definition fmap_FreeT
  {A B : Type} (f : A -> B) (x : FreeT F M A) : FreeT F M B :=
    fun X pure wrap => x X (f .> pure) wrap.

#[refine]
#[export]
Instance Functor_FreeT : Functor (FreeT F M) :=
{
    fmap := @fmap_FreeT
}.
Proof. all: reflexivity. Defined.

Definition pure_FreeT
  {A : Type} (x : A) : FreeT F M A :=
    fun X pure _ => pure x.

Definition ap_FreeT
  {A B : Type} (mf : FreeT F M (A -> B)) (ma : FreeT F M A) : FreeT F M B :=
    fun X pure wrap => mf X (fun f => fmap f ma X pure wrap) wrap.

#[refine]
#[export]
Instance Applicative_FreeT : Applicative (FreeT F M) :=
{
    pure := @pure_FreeT;
    ap := @ap_FreeT;
}.
Proof. all: reflexivity. Defined.

Definition bind_FreeT
  {A B : Type} (x : FreeT F M A) (f : A -> FreeT F M B) : FreeT F M B :=
    fun X pure wrap => x X (fun a => f a X pure wrap) wrap.

#[refine]
#[export]
Instance Monad_FreeT : Monad (FreeT F M) :=
{
    bind := @bind_FreeT
}.
Proof. all: reflexivity. Defined.

End FreeT.

(** Free monad isn't [Alternative], because it doesn't have anything more
    than what is needed to be a monad. *)
Lemma FreeT_not_Alternative :
  (forall (F : Type -> Type) (M : Type -> Type) (inst : Monad M),
    Alternative (FreeT F M)) -> False.
Proof.
  intro H. destruct (H Identity Identity _).
  unfold FreeT, Identity in *.
  apply (aempty False False); trivial.
Qed.

(** We can lift a computation into the monad by binding it to the
    "constructor" [pure]. *)
Definition lift_FreeT
  {F M : Type -> Type} {inst : Monad M} {A : Type}
  (x : M A) : FreeT F M A :=
    fun X pure wrap => x >>= pure.

#[global] Hint Unfold fmap_FreeT pure_FreeT ap_FreeT bind_FreeT lift_FreeT : CoqMTL.

#[refine]
#[export]
Instance MonadTrans_FreeT
  {F : Type -> Type} : MonadTrans (FreeT F) :=
{
    is_monad := fun M _ => @Monad_FreeT F M;
    lift := @lift_FreeT F;
}.
Proof. all: monad. Defined.

(** [FreeT F M] adds a layer of the free monad for [F] on top of [M]. *)
#[refine]
#[export]
Instance MonadFree_FreeT
  (F : Type -> Type) (instF : Functor F)
  (M : Type -> Type) (instM : Monad M)
  : MonadFree F (FreeT F M) instF (Monad_FreeT F M) :=
{
    wrap :=
      fun A x =>
        fun X pure wrap => wrap (fmap (fun x => x X pure wrap) x)
}.
Proof.
  monad. rewrite <- !fmap_comp'. unfold compose. reflexivity.
Defined.

(** [FreeT] in respect to classes behaves quite similarly to [ContT] -
    it preserves [MonadNondet], [MonadReader], [MonadWriter], [MonadState],
    but doesn't preserve [MonadExcept] nor [MonadStateNondet]. The reasons
    for this are also quite similar: definitions of some functions don't
    at all refer to the underlying monad's [pure] or [bind]. *)

#[refine]
#[export]
Instance MonadAlt_FreeT
  (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (FreeT F M) (Monad_FreeT F M) :=
{
    choose :=
      fun A x y => fun X pure wrap => choose (x X pure wrap) (y X pure wrap)
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadFail_FreeT
  (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (FreeT F M) (Monad_FreeT F M) :=
{
    fail := fun A => fun X pure wrap => fail
}.
Proof. reflexivity. Defined.

#[refine]
#[export]
Instance MonadNondet_FreeT
  (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (FreeT F M) (Monad_FreeT F M) :=
{
    instF := @MonadFail_FreeT F M inst (@instF _ _ inst');
    instA := @MonadAlt_FreeT F M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

#[refine]
#[export]
Instance MonadExcept_FreeT
  (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (FreeT F M) (Monad_FreeT F M) :=
{
    instF := @MonadFail_FreeT F M inst inst';
    catch :=
      fun A x y =>
        fun X pure wrap => catch (x X pure wrap) (y X pure wrap)
}.
Proof.
  all: monad.
Abort.

#[refine]
#[export]
Instance MonadReader_FreeT
  (E : Type) (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (FreeT F M) (Monad_FreeT F M) :=
{
    ask := fun X pure wrap => ask >>= pure
}.
Proof.
  ext3 X pure wrap. cbn.
  unfold fmap_FreeT, const, id, compose.
  rewrite <- bind_assoc.
  rewrite <- constrA_spec, ask_ask. reflexivity.
Defined.

#[refine]
#[export]
Instance MonadWriter_FreeT
  (W : Monoid) (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadWriter W M inst)
  : MonadWriter W (FreeT F M) (Monad_FreeT F M) :=
{
    tell w := fun X pure wrap => tell w >>= pure;
    listen :=
      fun A x =>
        fun X pure wrap => x X (fun a => pure (a, neutr)) wrap
}.
Proof. all: reflexivity. Defined.

#[refine]
#[export]
Instance MonadState_FreeT
  (S : Type) (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (FreeT F M) (Monad_FreeT F M) :=
{
    get := fun X pure wrap => get >>= pure;
    put := fun s => fun X pure wrap => put s >>= pure;
}.
Proof.
  monad;
    unfold const, id, compose; monad.
  intros. ext3 X pure wrap. cbn.
    hs. unfold const, id, compose. rewrite <- bind_assoc.
    rewrite put_get'. monad.
  intros. ext3 X pure wrap. cbn.
    unfold bind_FreeT, pure_FreeT.
    rewrite <- bind_assoc, get_put. hs.
  monad.
Defined.

#[refine]
#[export]
Instance MonadStateNondet_FreeT
  (S : Type) (F : Type -> Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (FreeT F M) (Monad_FreeT F M) :=
{
    instS := MonadState_FreeT S F M inst inst';
    instN := MonadNondet_FreeT F M inst inst';
}.
Proof.
  all: monad.
Abort.