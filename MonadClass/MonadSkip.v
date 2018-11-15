Require Import HSLib.Base.
Require Import Control.
Check @aempty.
(*
Class MonadSkip (M : Type -> Type) (inst : Monad M) : Type :=
{
    skip : forall {A : Type}, M A;
    bind_skip_l :
      forall (A B : Type) (f : A -> M B),
        skip >>= f = f;
    bind_skip_r :
      forall (A : Type) (x : M A),
        x >> skip = x;
}.
*)