Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.MonadTrans.

Require Import HSLib.Instances.All.


Definition WriterT (W : Monoid) (M : Type -> Type) (A : Type)
  : Type := M (A * W)%type.

Definition fmap_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> B)
  (x : WriterT W M A) : WriterT W M B :=
    fmap (fun '(a, w) => (f a, w)) x.

Hint Unfold WriterT fmap_WriterT compose (* BEWARE *): HSLib.

Instance Functor_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} : Functor (WriterT W M) :=
{
    fmap := @fmap_WriterT W M inst
}.
Proof.
  all: monad.
Defined.

Definition pure_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : WriterT W M A := pure (x, neutr).

Definition ap_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mf : WriterT W M (A -> B)) (mx : WriterT W M A) : WriterT W M B :=
    @bind M inst _ _ mf (fun '(f, w) =>
    @bind M inst _ _ mx (fun '(x, w') =>
      pure (f x, op w w'))).

Hint Unfold pure_WriterT ap_WriterT : HSLib.

Instance Applicative_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M)
  : Applicative (WriterT W M) :=
{
    is_functor := @Functor_WriterT W M inst;
    pure := @pure_WriterT W M inst;
    ap := @ap_WriterT W M inst;
}.
Proof. all: monad. Defined.

Theorem WriterT_not_Alternative :
  (forall (W : Monoid) (M : Type -> Type) (inst : Monad M),
    Alternative (WriterT W M)) -> False.
Proof.
  intros. assert (W : Monoid).
    refine {| carr := unit; neutr := tt; op := fun _ _ => tt |}.
      1-3: try destruct x; reflexivity.
    destruct (X W Identity MonadIdentity).
    clear -aempty. specialize (aempty False).
    compute in aempty. destruct aempty. assumption.
Qed.

Definition aempty_WriterT
  (W : Monoid) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : WriterT W M A := fmap (fun a => (a, neutr)) aempty.

Definition aplus_WriterT
  {W : Monoid} {M : Type -> Type} {inst : MonadPlus M} {A : Type}
  (wx wy : WriterT W M A) : WriterT W M A :=
    @aplus M inst _ wx wy.

Hint Unfold aempty_WriterT aplus_WriterT : HSLib.

Instance Alternative_WriterT
  (W : Monoid) (M : Type -> Type) (inst : MonadPlus M)
  : Alternative (WriterT W M) :=
{
    is_applicative := Applicative_WriterT W M inst;
    aempty := @aempty_WriterT W M inst inst;
    aplus := @aplus_WriterT W M inst;
}.
Proof. all: monad. Defined.

Definition bind_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : WriterT W M A) (f : A -> WriterT W M B) : WriterT W M B :=
    @bind M inst _ _ x (fun '(a, w) =>
    @bind M inst _ _ (f a) (fun '(b, w') =>
      pure (b, op w w'))).

Hint Unfold bind_WriterT : HSLib.

Instance Monad_WriterT
  (W : Monoid) (M : Type -> Type) {inst : Monad M} : Monad (WriterT W M) :=
{
    is_applicative := @Applicative_WriterT W M inst;
    bind := @bind_WriterT W M inst;
}.
Proof. all: monad. Defined.

Theorem WriterT_not_MonadPlus :
  (forall (W : Monoid) (M : Type -> Type) (inst : Monad M),
    MonadPlus (WriterT W M)) -> False.
Proof.
  intros. apply WriterT_not_Alternative.
  intros. destruct (X W M inst). assumption.
Qed.

Instance MonadPlus_WriterT
  (W : Monoid) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (WriterT W M) :=
{
    is_monad := @Monad_WriterT W M inst;
    is_alternative := @Alternative_WriterT W M inst;
}.
Proof. monad. Defined.

Definition lift_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : WriterT W M A := fmap (fun x : A => (x, neutr)) ma.

Hint Unfold lift_WriterT : HSLib.

Instance MonadTrans_WriterT (W : Monoid) : MonadTrans (WriterT W) :=
{
    is_monad := @Monad_WriterT W;
    lift := @lift_WriterT W;
}.
Proof. all: monad. Defined.