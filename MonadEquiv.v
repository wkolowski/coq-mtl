Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Module Join.
Require Import HSLib.MonadJoin.Monad.
Include HSLib.MonadJoin.Monad.
End Join.

Module Bind.
Require Import HSLib.MonadBind.Monad.
Include HSLib.MonadBind.Monad.
End Bind.

Module Comp.
Require Import HSLib.MonadComp.Monad.
Include HSLib.MonadComp.Monad.
End Comp.
Print Bind.Monad.
Instance JoinToBind (M : Type -> Type) (inst : Join.Monad M) : Bind.Monad M :=
{
    is_functor := @Join.is_functor M inst;
    ret := @Join.ret M inst;
    bind := fun (A B : Type) (ma : M A) (f : A -> M B) =>
        (fmap f .> Join.join) ma
}.
Proof.
Abort.