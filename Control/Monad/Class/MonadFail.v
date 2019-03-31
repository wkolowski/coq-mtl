Require Export Control.Monad.

(** A monad which models computations that can fail. If a computation
    fails, any later computation that depends on it also fails, as
    exhibited by the law [bind_fail_l]. *)
Class MonadFail (M : Type -> Type) (inst : Monad M) : Type :=
{
    fail : forall {A :  Type}, M A;
    bind_fail_l :
      forall (A B : Type) (f : A -> M B),
        fail >>= f = fail
}.

Hint Rewrite @bind_fail_l : HSLib.

Set Implicit Arguments.

Section MonadFailFuns.

Variables M : Type -> Type.
Variable instM : Monad M.
Variable instMF : MonadFail M instM.

(** We can "filter" a computation by running it and then wrapping
    values that satisfy the given boolean predicate in [pure] and
    turning the ones that don't into [fail]s. *)
Definition mfilter {A : Type} (p : A -> bool) (ma : M A) : M A :=
  ma >>= fun a : A => if p a then pure a else fail.

(** Using [mfilter], we can partition a computation into two computations
    that satisfy and don't satisfy a predicate [p], respectively. *)
Definition mpartition {A : Type} (p : A -> bool) (ma : M A) : M A * M A :=
  (mfilter p ma, mfilter (p .> negb) ma).

(** We can turn an optional value of type [A] into a computation by
    treating [Some] as success and [None] as failure. Thnaks to this,
    we can turn computations that return [option A] into ones that
    return just [A]. We can use this for mapping partial functions
    over our computations. *)

Definition fromOption {A : Type} (oa : option A) : M A :=
match oa with
    | None => fail
    | Some a => pure a
end.

Definition mcatOptions {A : Type} (x : M (option A)) : M A :=
  x >>= fromOption.

Definition mmapOption {A B : Type} (f : A -> option B) (x : M A) : M B :=
  mcatOptions (fmap f x).

(** Similarly, we can split a computation that returns a sum into two
    computations that return the left and right component of the sum. *)

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

End MonadFailFuns.

Arguments mfilter {M instM instMF A} _ _.
Arguments mpartition {M instM instMF A} _ _.
Arguments mcatOptions {M instM instMF A} _.