Require Import Control.

Definition RoseTreeT (M : Type -> Type) (A : Type) : Type :=
  forall X : Type, (A -> M X) -> (M X -> M X -> M X) -> M X.

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

Require Import HSLib.Control.Monad.All.

Theorem RoseTreeT_not_Alternative :
  (forall (M : Type -> Type) (inst : Monad M), Alternative (RoseTreeT M)) ->
    False.
Proof.
  unfold RoseTreeT; intros.
  specialize (X Identity (MonadIdentity)).
  unfold Identity in *. destruct X.
  apply (aempty False False); trivial.
Qed.

Theorem RoseTreeT_not_MonadPlus :
  (forall (M : Type -> Type) (inst : Monad M), MonadPlus (RoseTreeT M)) ->
  False.
Proof.
  intros. apply RoseTreeT_not_Alternative, X.
Qed.

Require Import Control.Monad.Class.All.

Instance MonadAlt_RoseTreeT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    choose :=
      fun A x y =>
        fun X empty node => choose (x X empty node) (y X empty node)
}.
Proof.
  monad.
  reflexivity.
Defined.

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
Proof.
  intros. cbn. ext X. ext e. ext n. rewrite choose_fail_l. reflexivity.
  intros. cbn. ext X. ext e. ext n. rewrite choose_fail_r. reflexivity.
Defined.

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
  all: cbn; intros; ext X; ext empty; ext node.
    apply catch_fail_l.
    apply catch_fail_r.
    apply catch_assoc.
    unfold pure_RoseTreeT.
Abort.

Instance MonadReader_RoseTreeT
  (E : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    ask := fun X empty node => ask >>= empty
}.
Proof.
  ext X. ext empty. ext node. cbn. unfold fmap_RoseTreeT, const, id, compose.
  rewrite <- constrA_spec, constrA_bind_assoc, ask_ask. reflexivity.
Defined.

Instance MonadState_RoseTreeT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (RoseTreeT M) (Monad_RoseTreeT M) :=
{
    get := fun X empty node => get >>= empty;
    put := fun s X empty node => put s >> empty tt;
}.
Proof.
  intros. ext X. ext empty. ext node. cbn.
    unfold fmap_RoseTreeT, const, id, compose.
    rewrite <- constrA_assoc, put_put. reflexivity.
  intros. ext X. ext empty. ext node. cbn.
    unfold fmap_RoseTreeT, const, id, compose, pure_RoseTreeT.
    rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc, bind_pure_l.
    reflexivity.
  intros. ext X. ext empty. ext node. cbn.
    unfold bind_RoseTreeT, pure_RoseTreeT.
    rewrite bind_constrA_comm, get_put, constrA_pure_l.
Admitted.

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
    unfold bind_RoseTreeT. ext X. ext empty. ext node.
Abort.

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