Require Export HSLib.Control.Alternative.
Require Export HSLib.Control.Monad.
Require Export HSLib.Control.Foldable.

(** A functor that is both a [Monad] and an [Alternative]. The intended
    categorical semantics are unclear (strong monoidal monad with a bonus
    monoid structure?).

    Loosely based on Haskell's MonadPlus, but this is not yet well-developed.
    There's only one law to make sure that [aempty] is the left annihilator
    of [>>=]. The other law given in Haskell's standard library, namely
    [x >> aempty = aempty] is not present. *)
Class MonadPlus (M : Type -> Type) : Type :=
{
    is_monad :> Monad M;
    is_alternative :> Alternative M;
    bind_aempty_l :
      forall (A B : Type) (f : A -> M B),
        aempty >>= f = aempty;
(* Not satisfied by lists.
    bind_aempty_r :
      forall (A : Type) (x : M A),
        x >> aempty = x;
*)
}.

(** Note that there's yet nothing to make sure that the [Applicative] instance
    coming from [Monad] is the same as the one coming from [Alternative]. This
    gives the warning "ambiguous paths". *)
Coercion is_monad : MonadPlus >-> Monad.
Coercion is_alternative : MonadPlus >-> Alternative.

Hint Rewrite @bind_aempty_l : HSLib.

(** Functions from Haskell's Control.Monad.Plus, but without the ones that
    can be generalized to [Alternative]. *)
Section MonadPlusFunctions1.

Variables M T : Type -> Type.
Variable instM : MonadPlus M.
Variable instT : Foldable T.
Variables A B C : Type.

Definition mfilter (f : A -> bool) (ma : M A) : M A :=
  ma >>= fun a : A => if f a then pure a else aempty.

Definition mpartition (p : A -> bool) (ma : M A) : M A * M A :=
  (mfilter p ma, mfilter (p .> negb) ma).

Definition mcatOptions (x : M (option A)) : M A :=
  x >>= @aFromOption _ _ _.

Definition mscatter (x : M (T A)) : M A :=
    x >>= @afold _ _ _ _ _.

End MonadPlusFunctions1.

Arguments mfilter {M instM A} _ _.
Arguments mpartition {M instM A} _ _.
Arguments mcatOptions {M instM A} _.
Arguments mscatter {M T instM instT A} _.

Section MonadPlusFunctions2.

Variables M T : Type -> Type.
Variable instM : MonadPlus M.
Variable instT : Foldable T.
Variables A B C : Type.

Definition sum_left (x : A + B) : option A :=
match x with
    | inl a => Some a
    | _ => None
end.

Definition sum_right (x : A + B) : option B :=
match x with
    | inr b => Some b
    | _ => None
end.

Definition mlefts (x : M (A + B)) : M A :=
  mcatOptions (fmap sum_left x).

Definition mrights (x : M (A + B)) : M B :=
  mcatOptions (fmap sum_right x).

Definition mpartitionEithers (x : M (A + B)) : M A * M B :=
  (mlefts x, mrights x).

Definition mmapOption (f : A -> option B) (x : M A) : M B :=
  mcatOptions (fmap f x).

Definition mconcatMap (f : A -> T B) (x : M A) : M B :=
  mscatter (fmap f x).

End MonadPlusFunctions2.