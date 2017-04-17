Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export Functor.
Require Export FunctorInst.

Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    ret : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B
}.

Coercion is_functor : Monad >-> Functor.

Definition join {M : Type -> Type} {_inst : Monad M} {A : Type}
    (mma : M (M A)) : M A := bind mma id.

Definition compM {M : Type -> Type} {_inst : Monad M} {A B C: Type}
    (f : A -> M B) (g : B -> M C) (a : A) : M C :=
    bind (bind (ret a) f) g.

Module MonadNotations.
Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).
End MonadNotations.

Export MonadNotations.