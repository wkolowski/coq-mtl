Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Base.
Require Export HSLib.MonadJoin.Monad.

Inductive Lazy (A : Type) : Type :=
    | thunk : forall t : unit -> A, Lazy A
    | thunk' : forall t : unit -> Lazy A, Lazy A.

Arguments thunk [A] _.
Arguments thunk' [A] _.

Fixpoint force {A : Type} (la : Lazy A) : A :=
match la with
    | thunk t => t tt
    | thunk' t => force (t tt)
end.

