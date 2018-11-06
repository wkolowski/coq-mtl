Require Import Control.

Require Import HSLib.Instances.All.

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
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (ReaderT E M) :=
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
  (E : Type) (M : Type -> Type) {inst : Monad M} : Monad (ReaderT E M) :=
{
    is_applicative := @Applicative_ReaderT E M inst;
    bind := @bind_ReaderT M inst E;
}.
Proof. all: monad. Defined.

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