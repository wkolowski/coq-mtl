Require Import HSLib.Base.
Require Import Control.Monad.

Require Import MonadClass.MonadFail.
Require Import MonadClass.MonadAlt.

Class MonadNondet (M : Type -> Type) (inst : Monad M) : Type :=
{
    instF :> MonadFail M inst;
    instA :> MonadAlt M inst;
    choose_fail_l :
      forall (A : Type) (x : M A),
        choose fail x = x;
    choose_fail_r :
      forall (A : Type) (x : M A),
        choose x fail = x;
}.