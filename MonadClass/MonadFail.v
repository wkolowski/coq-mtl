Require Import HSLib.Base.
Require Import Control.Monad.
Require Import Control.Alternative.
Require Import Control.Foldable.

Class MonadFail (M : Type -> Type) (inst : Monad M) : Type :=
{
    fail : forall {A :  Type}, M A;
    bind_fail_l :
      forall (A B : Type) (f : A -> M B),
        fail >>= f = fail
}.

Set Implicit Arguments.

Section MonadFailFuns.

Variables M : Type -> Type.
Variable instM : Monad M.
Variable instMF : MonadFail M instM.

Definition mfilter {A : Type} (f : A -> bool) (ma : M A) : M A :=
  ma >>= fun a : A => if f a then pure a else fail.

Definition mpartition {A : Type} (p : A -> bool) (ma : M A) : M A * M A :=
  (mfilter p ma, mfilter (p .> negb) ma).

Definition fromOption {A : Type} (oa : option A) : M A :=
match oa with
    | None => fail
    | Some a => pure a
end.

Definition mcatOptions {A : Type} (x : M (option A)) : M A :=
  x >>= fromOption.
Print afold.

(** TODO: threw away mscatter and mconcatMap *)

Definition sum_left {A B : Type} (x : A + B) : option A :=
match x with
    | inl a => Some a
    | _ => None
end.

Definition sum_right {A B : Type} (x : A + B) : option B :=
match x with
    | inr b => Some b
    | _ => None
end.

Definition mlefts {A B : Type} (x : M (A + B)) : M A :=
  mcatOptions (fmap sum_left x).

Definition mrights {A B : Type} (x : M (A + B)) : M B :=
  mcatOptions (fmap sum_right x).

Definition mpartitionSums {A B : Type} (x : M (A + B)) : M A * M B :=
  (mlefts x, mrights x).

Definition mmapOption {A B : Type} (f : A -> option B) (x : M A) : M B :=
  mcatOptions (fmap f x).

End MonadFailFuns.
Print mfilter.
Check mfilter _.
Arguments mfilter : default implicits.
Check mfilter.
Arguments mfilter {M instM instMF A} _ _.
Check mfilter.
Arguments mpartition {M instM instMF A} _ _.
Arguments mcatOptions {M instM instMF A} _.

Require Import Control.MonadTrans.

Print MonadTrans.

Variables
  (T : (Type -> Type) -> Type -> Type) (instT : MonadTrans T)
  (M : Type -> Type) (instM : Monad M)
  (instMF : MonadFail M instM).

Instance MonadFail_MonadTrans : MonadFail (T M) (is_monad M instM).
Proof.
  esplit. Unshelve.
    Focus 2. intro. exact (lift fail). Check @pure (T M) (is_monad _ instM).
    monad.
    replace fail with (@constrA M instM A A fail fail).
      rewrite <- lift_constrA. rewrite constrA_spec.
      rewrite bind_assoc. Print MonadTrans.

Abort.