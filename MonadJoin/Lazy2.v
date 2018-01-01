Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.MonadJoin.Monad.

Set Universe Polymorphism.

Inductive Lazy : Type -> Type :=
    | thunk : forall A : Type, (unit -> A) -> Lazy A
(*    | fmap_Lazy : forall A B : Type, (A -> B) -> Lazy A -> Lazy B*)
    | bind_Lazy : forall A B : Type, Lazy A -> (A -> Lazy B) -> Lazy B.

Arguments thunk [A] _.
(*Arguments fmap_Lazy [A B ] _ _.*)
Arguments bind_Lazy [A B ] _ _.

Fixpoint force {A : Type} (la : Lazy A) : A :=
match la with
    | thunk f => f tt
(*    | fmap_Lazy f la => f (force la)*)
    | bind_Lazy la f => force (f (force la))
end.

(*Fixpoint fmap_Lazy {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
match la with
    | thunk t => thunk (fun _ => f (t tt))
    | bind_Lazy la g => 

Definition join {A : Type} (lla : Lazy (Lazy A)) : Lazy A :=
  force lla.

Instance FunctorLazy : Functor Lazy :=
{
    fmap := @fmap_Lazy;
}.
Proof.
  intro. 
*)

(*Eval lazy in bind (val 5) (fun n => val (n + n)).
Eval lazy in bind (val 5) (fun n => thunk (fun u : unit => n + n)).
Eval lazy in bind (thunk (fun _ => 5)) (fun n => thunk (fun u : unit => n + n)).
*)