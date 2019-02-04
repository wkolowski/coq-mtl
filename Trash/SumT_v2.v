Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition SumT (E : Type) (M : Type -> Type) (A : Type)
  : Type := sum E (M A).

Definition fmap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  (ema : SumT E M A) : SumT E M B :=
  match ema with
      | inl e => inl e
      | inr a => inr (fmap f a)
  end.

Hint Unfold SumT fmap_SumT : HSLib.

Instance Functor_SumT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (SumT E M) :=
{
    fmap := @fmap_SumT M inst E
}.
Proof.
  all: hs; mtrans; monad. f_equal. monad.
Defined.

Definition pure_SumT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A) : SumT E M A :=
    inr (pure x).

Definition ap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (emf : SumT E M (A -> B)) (emx : SumT E M A) : SumT E M B :=
  match emf, emx with
      | inl e, _ => inl e
      | _, inl e => inl e
      | inr mf, inr mx => inr (ap mf mx)
  end.

Hint Unfold pure_SumT ap_SumT : HSLib.

Instance Applicative_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (SumT E M) :=
{
    is_functor := @Functor_SumT M inst E;
    pure := @pure_SumT M inst E;
    ap := @ap_SumT M inst E;
}.
Proof.
  all: hs; monad; f_equal; monad.
Defined.

Lemma SumT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (SumT E M)) -> False.
Proof.
  intros. destruct (X False Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. destruct aempty; assumption.
Qed.

Definition aempty_SumT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : SumT E M A := inr aempty.

Definition aplus_SumT
  {E : Type} {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (emx emy : SumT E M A) : SumT E M A :=
    match emx, emy with
        | inl e, _ => inl e
        | _, inl e => inl e
        | inr x, inr y => inr (aplus x y)
    end.

Hint Unfold aempty_SumT aplus_SumT : HSLib.

Instance Alternative_SumT
  (E : Type) (M : Type -> Type) (inst : MonadPlus M)
  : Alternative (SumT E M) :=
{
    is_applicative := Applicative_SumT E M inst;
    aempty := @aempty_SumT E M inst inst;
    aplus := @aplus_SumT E M inst inst;
}.
Proof.
  all: hs.
    destruct fa; f_equal; hs.
    destruct fa; f_equal; hs.
    destruct x, y, z; hs.
Defined.

Lemma sumt_not_Monad :
  exists (E : Type) (M : Type -> Type) (inst : Monad M),
    Monad (SumT E M) -> False.
Proof.
  Require Import Control.Monad.Option.
  exists False, Identity, MonadIdentity. (* option, MonadOption.*)
  destruct 1. clear - bind.
  specialize (bind unit False). compute in bind.
Abort.

Definition bind_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (ema : SumT E M A) (f : A -> SumT E M B) : SumT E M B.
Proof.
  destruct ema.
    exact (inl e).
    Check fmap f m.
    apply f.
Abort.

(* TODO
Hint Unfold bind_SumT : HSLib.

Instance Monad_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} : Monad (SumT E M) :=
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
*)