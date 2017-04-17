Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import HSLib.MonadJoin.Monad.

Class MonadTrans (T : Type -> Type) : Type :=
{
    lift : forall (M : Type -> Type) {_inst : Monad M} {A : Type},
        M A -> M (T A);
    is_monad : forall (M : Type -> Type),
        Monad M -> Monad (fun A : Type => M (T A))
(*    law1 : forall (M : Type -> Type) (_ : Monad M),
        forall (A : Type) (x : A), lift M (ret x) = ret x*)
}.

Arguments lift _ [_] [M] [_inst] [A] _.