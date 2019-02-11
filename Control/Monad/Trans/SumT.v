Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition SumT (E : Type) (M : Type -> Type) (A : Type)
  : Type := M (sum E A).

Definition fmap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  : SumT E M A -> SumT E M B :=
    fmap (fun sa : sum E A =>
    match sa with
        | inl e => inl e
        | inr a => inr (f a)
    end).

Hint Unfold SumT fmap_SumT : HSLib.

Instance Functor_SumT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (SumT E M) :=
{
    fmap := @fmap_SumT M inst E
}.
Proof. all: hs; mtrans; monad. Defined.

Definition pure_SumT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A)
  : SumT E M A := pure (inr x).

Definition ap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (msf : SumT E M (A -> B)) (msx : SumT E M A) : SumT E M B :=
    @bind M inst _ _ msf (fun sf =>
      match sf with
          | inl e => pure (inl e)
          | inr f =>
              @bind M inst _ _ msx (fun sx =>
              match sx with
                  | inl e => pure (inl e)
                  | inr x => pure (inr (f x))
              end)
      end).

Hint Unfold pure_SumT ap_SumT : HSLib.

Instance Applicative_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (SumT E M) :=
{
    is_functor := @Functor_SumT M inst E;
    pure := @pure_SumT M inst E;
    ap := @ap_SumT M inst E;
}.
Proof. all: hs; monad. Defined.

Theorem SumT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (SumT E M)) -> False.
Proof.
  intros. destruct (X False Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. destruct aempty; assumption.
Qed.

Definition aempty_SumT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : SumT E M A := fmap inr aempty.

Definition aplus_SumT
  {E : Type} {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (x y : SumT E M A) : SumT E M A :=
    @aplus _ instA _ x y.

Hint Unfold aempty_SumT aplus_SumT : HSLib.

Instance Alternative_SumT
  (E : Type) (M : Type -> Type) (inst : MonadPlus M)
  : Alternative (SumT E M) :=
{
    is_applicative := Applicative_SumT E M inst;
    aempty := @aempty_SumT E M inst inst;
    aplus := @aplus_SumT E M inst inst;
}.
Proof. all: hs. Defined.

Definition bind_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (ma : SumT E M A) (f : A -> SumT E M B) : SumT E M B :=
    @bind M inst _ _ ma (fun sa : E + A =>
    match sa with
        | inl e => pure (inl e)
        | inr a => f a
    end).

Hint Unfold bind_SumT : HSLib.

Instance Monad_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Monad (SumT E M) :=
{
    is_applicative := @Applicative_SumT E M inst;
    bind := @bind_SumT M inst E;
}.
Proof. all: hs; monad. Defined.

Theorem SumT_not_MonadPlus :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (SumT E M)) -> False.
Proof.
  intros. apply SumT_not_Alternative.
  intros. destruct (X E M inst). assumption.
Qed.

Instance MonadPlus_SumT
  (E : Type) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (SumT E M) :=
{
    is_monad := @Monad_SumT E M inst;
    is_alternative := @Alternative_SumT E M inst;
}.
Proof. hs. Defined.

Definition lift_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
  : SumT E M A := fmap inr ma.

Hint Unfold lift_SumT : HSLib.

Instance MonadTrans_SumT (E : Type) : MonadTrans (SumT E) :=
{
    is_monad := @Monad_SumT E;
    lift := @lift_SumT E;
}.
Proof. all: hs; monad. Defined.

Require Import Control.Monad.Class.All.

Definition fail_SumT
  {E : Type} {M : Type -> Type} {inst : Monad M} (e : E) {A : Type}
    : SumT E M A := pure $ inl e.

Instance MonadFail_SumT
  (E : Type) (M : Type -> Type) {inst : Monad M} (e : E)
  : MonadFail (SumT E M) (Monad_SumT E M inst) :=
{
    fail := @fail_SumT E M inst e
}.
Proof. intros. unfold fail_SumT. monad. Defined.

Instance MonadExcept_SumT
  (E : Type) (e : E) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (SumT E M) (Monad_SumT E M inst) :=
{
    instF := @MonadFail_SumT E M inst e;
    catch :=
      fun A x y =>
      @bind M inst _ _ x (fun ea =>
      match ea with
          | inl e => y (*pure (inl e)*)
          | inr _ => x
      end)
}.
Proof.
  all: cbn; intros.
    unfold fail_SumT. rewrite bind_pure_l. reflexivity.
    rewrite <- (@bind_pure_r M inst _ x) at 2.
      f_equal. ext ea.
    Focus 2. rewrite bind_assoc.
Abort.