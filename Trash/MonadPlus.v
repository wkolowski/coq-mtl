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

Definition mscatter (x : M (T A)) : M A :=
    x >>= @afold _ _ _ _ _.

End MonadPlusFunctions1.

Arguments mscatter {M T instM instT A} _.

Section MonadPlusFunctions2.

Variables M T : Type -> Type.
Variable instM : MonadPlus M.
Variable instT : Foldable T.
Variables A B C : Type.


Definition mconcatMap (f : A -> T B) (x : M A) : M B :=
  mscatter (fmap f x).

End MonadPlusFunctions2.