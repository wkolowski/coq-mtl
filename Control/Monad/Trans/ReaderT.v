Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition ReaderT (E : Type) (M : Type -> Type) (A : Type)
  : Type := E -> M A.

Definition fmap_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  : ReaderT E M A -> ReaderT E M B :=
    fun (x : ReaderT E M A) (e : E) => fmap f (x e).

Hint Unfold ReaderT fmap_ReaderT : HSLib.

Instance Functor_ReaderT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (ReaderT E M) :=
{
    fmap := @fmap_ReaderT M inst E
}.
Proof. all: monad. Defined.

Definition pure_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A)
  : ReaderT E M A := fun _ => pure x.

Definition ap_ReaderT
  {E : Type} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : ReaderT E M (A -> B)) (x : ReaderT E M A) : ReaderT E M B :=
    fun e : E => f e <*> x e.

Hint Unfold pure_ReaderT ap_ReaderT : HSLib.

Instance Applicative_ReaderT
  (E : Type) (M : Type -> Type) (inst : Monad M)
  : Applicative (ReaderT E M) :=
{
    is_functor := @Functor_ReaderT M inst E;
    pure := @pure_ReaderT M inst E;
    ap := @ap_ReaderT E M inst;
}.
Proof. all: monad. Defined.

Theorem ReaderT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (ReaderT E M)) -> False.
Proof.
  intros. destruct (X unit Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. apply aempty. exact tt.
Qed.

Definition aempty_ReaderT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : ReaderT E M A := fun _ => aempty.

Definition aplus_ReaderT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (x y : ReaderT E M A) : ReaderT E M A :=
    fun c => x c <|> y c.

Hint Unfold aempty_ReaderT aplus_ReaderT : HSLib.

Instance Alternative_ReaderT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  : Alternative (ReaderT E M) :=
{
    is_applicative := @Applicative_ReaderT E M instM;
    aempty := @aempty_ReaderT E M instM instA;
    aplus := @aplus_ReaderT E M instM instA;
}.
Proof. all: monad. Defined.

Definition bind_ReaderT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (x : ReaderT E M A) (f : A -> ReaderT E M B) : ReaderT E M B :=
    fun e : E => x e >>= (fun a : A => f a e).

Hint Unfold bind_ReaderT : HSLib.

Instance Monad_ReaderT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Monad (ReaderT E M) :=
{
    is_applicative := @Applicative_ReaderT E M inst;
    bind := @bind_ReaderT M inst E;
}.
Proof. all: monad. Defined.

(*
Theorem ReaderT_not_MonadPlus :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (ReaderT E M)) -> False.
Proof.
  intros. apply ReaderT_not_Alternative.
  intros. destruct (X E M inst). assumption.
Qed.

Instance MonadPlus_ReaderT
  (E : Type) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (ReaderT E M) :=
{
    is_monad := @Monad_ReaderT E M inst;
    is_alternative := @Alternative_ReaderT E M inst inst;
}.
Proof. all: monad. Defined.
*)

Definition lift_ReaderT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : ReaderT E M A := fun _ => ma.

Hint Unfold lift_ReaderT.

Instance MonadTrans_ReaderT (E : Type) : MonadTrans (ReaderT E) :=
{
    is_monad := @Monad_ReaderT E;
    lift := @lift_ReaderT E;
}.
Proof. all: reflexivity. Defined.

Require Import Control.Monad.Class.All.

Instance MonadReader_Reader
  (M : Type -> Type) (inst : Monad M) (R : Type)
  : MonadReader R (ReaderT R M) (Monad_ReaderT R M inst) :=
{
    ask := pure
}.
Proof. monad. Defined.

Require Import Control.Monad.Class.All.

Instance MonadAlt_ReaderT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (ReaderT R M) (Monad_ReaderT R M inst) :=
{
    choose :=
      fun A x y r => choose (x r) (y r)
}.
Proof. all: monad. Defined.

Instance MonadFail_ReaderT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (ReaderT R M) (Monad_ReaderT R M inst) :=
{
    fail := fun A r => fail
}.
Proof. monad. Defined.

Instance MonadNondet_ReaderT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (ReaderT R M) (Monad_ReaderT R M inst) :=
{
    instF := @MonadFail_ReaderT R M inst (@instF _ _ inst');
    instA := @MonadAlt_ReaderT R M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

Instance MonadExcept_ReaderT
  (E : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (ReaderT E M) (Monad_ReaderT E M inst) :=
{
    instF := @MonadFail_ReaderT E M inst inst';
    catch :=
      fun A x y => fun e => catch (x e) (y e);
}.
Proof. all: monad. Defined.

Instance MonadState_ReaderT
  (S R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (ReaderT R M) (Monad_ReaderT R M inst) :=
{
    get := fun r => get;
    put := fun s r => put s;
}.
Proof.
  intros. ext r. cbn. unfold ap_ReaderT, fmap_ReaderT, const, id. monad.
  intros. rewrite constrA_spec. cbn. monad.
  monad.
  intros. ext r. cbn. monad.
Defined.

Instance MonadStateNondet_ReaderT
  (E S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (ReaderT E M) (Monad_ReaderT E M inst) :=
{
    instS := MonadState_ReaderT S E M inst inst';
    instN := MonadNondet_ReaderT E M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn. unfold bind_ReaderT.
    ext e. rewrite <- constrA_spec. rewrite seq_fail_r. reflexivity.
  monad.
Defined.

Instance MonadFree_ReaderT
  (F : Type -> Type) (instF : Functor F)
  (E : Type) (M : Type -> Type)
  (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (ReaderT E M) instF (Monad_ReaderT E M instM) :=
{
    wrap :=
      fun A m e => wrap (fmap (fun x => x e) m)
}.
Proof.
  intros. ext e. cbn.
  unfold bind_ReaderT, pure_ReaderT, ReaderT in *.
  rewrite <- !fmap_comp'. unfold compose.
  apply wrap_law.
Defined.