Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.
Require Import HSLib.MonadJoin.Monad.

Definition ListT (M : Type -> Type) (A : Type) : Type := M (list A).

Section wut.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C : Type.

Definition ListT_fmap (f : A -> B) (x : M (list A)) : M (list B) :=
    fmap (fmap f) x.

Definition ListT_bind (x : M (list A)) (f : A -> M (list B)) : M (list B) :=
x >>= fix F (la : list A) :=
match la with
    | [] => ret []
    | h :: t => liftM2 (@app B) (f h) (F t)
end.

(*Check (fun x : M (list (M (list A))) => x >>= fun l => l).*)

(*Fixpoint ListT_join (x : M (list (M (list A)))) : M (list A) :=
x >>= fun lmla : list (M (list A)) =>
match lmla with
    | _ => ret []
end.
    | [] => ret []
    | mla :: mlas => (ListT_join (ret mlas)) 
end.*)

End wut.