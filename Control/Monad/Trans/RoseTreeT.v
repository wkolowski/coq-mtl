Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.
Require Import Control.Monad.Identity.

(** A transformer which adds some effect to the base monad [M], but I
    don't yet know what effect it is. It's completely analogous to
    the monad [RT], besides the fact that we can't use induction. *)
Definition RoseTreeT (M : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> M X) -> (M X -> M X -> M X) -> M X.

(** There most often is only one valid definition for a function. You can
    find it by following the types. *)

Section RoseTreeT_Instances.

Variable M : Type -> Type.
Variable inst : Monad M.

Definition fmap_RoseTreeT
  {A B : Type} (f : A -> B) (t : RoseTreeT M A) : RoseTreeT M B :=
    fun X leaf node => t X (f .> leaf) node.

Instance Functor_RoseTreeT : Functor (RoseTreeT M) :=
{
    fmap := @fmap_RoseTreeT
}.
Proof. all: reflexivity. Defined.

Definition pure_RoseTreeT
  {A : Type} (x : A) : RoseTreeT M A :=
    fun X leaf _ => leaf x.

Definition ap_RoseTreeT
  {A B : Type} (tf : RoseTreeT M (A -> B)) (ta : RoseTreeT M A)
  : RoseTreeT M B := fun X leaf node =>
    tf X (fun f => fmap f ta X leaf node) node.

Instance Applicative_RoseTreeT : Applicative (RoseTreeT M) :=
{
    pure := @pure_RoseTreeT;
    ap := @ap_RoseTreeT;
}.
Proof. all: reflexivity. Defined.

Definition bind_RoseTreeT
  {A B : Type} (ta : RoseTreeT M A) (tf : A -> RoseTreeT M B)
  : RoseTreeT M B := fun X leaf node =>
    ta X (fun a => tf a X leaf node) node.

Instance Monad_RoseTreeT : Monad (RoseTreeT M) :=
{
    bind := @bind_RoseTreeT
}.
Proof. all: reflexivity. Defined.

End RoseTreeT_Instances.

Hint Unfold
  fmap_RoseTreeT pure_RoseTreeT ap_RoseTreeT bind_RoseTreeT : HSLib.

(** [RoseTreeT M] isn't an [Alternative] functor precisely because the
    base monad [M] needs not be one. *)
Lemma RoseTreeT_not_Alternative :
  (forall (M : Type -> Type) (inst : Monad M), Alternative (RoseTreeT M)) ->
    False.
Proof.
  unfold RoseTreeT; intros.
  specialize (X Identity (Monad_Identity)).
  unfold Identity in *. destruct X.
  apply (aempty False False); trivial.
Qed.

(** But even if [M] is an [Alternative] functor, there still are some
    problems. *)
Instance Alternative_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : Alternative M)
  : Alternative (RoseTreeT M) :=
{
    is_applicative := @Monad_RoseTreeT M;
    aempty A := fun X leaf node => aempty >>= leaf;
    aplus A x y := fun X leaf node => aplus (x X leaf node) (y X leaf node)
}.
Proof.
  all: monad.
Abort.

(** [RoseTreeT] preserves [MonadNondet]. *)

Instance MonadAlt_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    choose :=
      fun A x y =>
        fun X empty node => choose (x X empty node) (y X empty node)
}.
Proof. all: monad. Defined.

Instance MonadFail_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    fail := fun A => fun X empty node => fail
}.
Proof. reflexivity. Defined.

Instance MonadNondet_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    instF := @MonadFail_RoseTreeT M inst (@instF _ _ inst');
    instA := @MonadAlt_RoseTreeT M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

(** [MonadExcept] poses the standard problem for Church-encoded
    transformers. *)
Instance MonadExcept_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    instF := @MonadFail_RoseTreeT M inst inst';
    catch :=
      fun A x y =>
        fun X empty node => catch (x X empty node) (y X empty node)
}.
Proof.
  1-3: monad.
    unfold pure_RoseTreeT.
Abort.

(** [RoseTreeT] preserves reader, writer and state. *)

Instance MonadReader_RoseTreeT
  (E : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    ask := fun X empty node => ask >>= empty
}.
Proof.
  ext3 X empty node. hs.
  rewrite <- ask_ask at 2.
  rewrite <- constrA_bind_assoc.
  monad.
Defined.

Instance MonadWriter_RoseTreeT
  (W : Monoid) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadWriter W M inst)
  : MonadWriter W (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    tell w := fun X leaf node => tell w >>= leaf;
    listen A x := fun X leaf node => x X (fun a => leaf (a, neutr)) node
}.
Proof. all: hs. Defined.

(** BEWARE: there is a strange bug when trying to prove the goals in order
    or [Focus] on the fourth goal. This is why we have to solve it first
    using the select 4: *)
Instance MonadState_RoseTreeT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    get := fun X empty node => get >>= empty;
    put := fun s X empty node => put s >> empty tt;
}.
Proof.
  4: intros; cbn; unfold bind_RoseTreeT; ext3 X leaf node; monad.
  monad.
  intros. ext3 X empty node. cbn.
    unfold fmap_RoseTreeT, const, id, compose, pure_RoseTreeT.
    rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc, bind_pure_l.
    reflexivity.
  intros. ext3 X empty node. cbn. hs.
    unfold bind_RoseTreeT, pure_RoseTreeT.
    rewrite bind_constrA_comm, get_put, constrA_pure_l. reflexivity.
Defined.

(** Even though [RoseTreeT] preserves both [MonadState] and [MonadNondet],
    [MonadStateNondet] poses standard problems. *)
Instance MonadStateNondet_RoseTreeT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    instS := MonadState_RoseTreeT S M inst inst';
    instN := MonadNondet_RoseTreeT M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn.
    unfold bind_RoseTreeT. ext X. ext2 empty node.
Abort.

(** If [M] is the free monad of [F], so is [RoseTreeT M]. *)
Instance MonadFree_RoseTreeT
  (F : Type -> Type) (instF : Functor F)
  (M : Type -> Type) (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (RoseTreeT M) instF (Monad_RoseTreeT M) :=
{
    wrap :=
      fun A fma X empty node =>
        wrap (fmap (fun l => l X empty node) fma)
}.
Proof.
  intros A B f x. ext3 X empty node.
  cbn. unfold bind_RoseTreeT, pure_RoseTreeT.
  rewrite <- !fmap_comp'. unfold compose.
  reflexivity.
Defined.