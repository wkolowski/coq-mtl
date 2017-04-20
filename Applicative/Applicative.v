Add LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Functor.FunctorInst.

(*Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.

Notation "f $ x" := (apply f x) (at level 30, right associativity).*)

Class Applicative (F : Type -> Type) : Type :=
{
    is_functor : Functor F;
    ret : forall {A : Type}, A -> F A;
    ap : forall {A B : Type}, F (A -> B) -> F A -> F B;
    identity : forall (A : Type) (ax : F A),
        ap (ret id) ax = ax;
    composition : forall (A B C : Type)
        (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
            ap (ap (ap (ret compose) ag) af) ax = ap ag (ap af ax);
    homomorphism : forall (A B : Type)
        (f : A -> B) (x : A), ap (ret f) (ret x) = ret (f x);
    interchange : forall (A B : Type) (f : F (A -> B)) (x : A),
        ap f (ret x) = ap (ret (fun f => f x)) f
}.
Print Applicative. Print Functor.
Coercion is_functor : Applicative >-> Functor.

Section ApplicativeFuns.

Variable F : Type -> Type.
Variable _inst : Applicative F.
Variables A B C D : Type.

Definition liftA (f : A -> B) (fa : F A)
    : F B := ap (ret f) fa.
Definition liftA2 (f : A -> B -> C) (fa : F A) (fb : F B)
    : F C := ap (ap (ret f) fa) fb.
Definition liftA3 (f : A -> B -> C -> D) (fa : F A) (fb : F B) (fc : F C)
    : F D := ap (ap (ap (ret f) fa) fb) fc.

End ApplicativeFuns.

Arguments liftA [F] [_inst] [A] [B] _ _.
Arguments liftA2 [F] [_inst] [A] [B] [C] _ _ _.
Arguments liftA3 [F] [_inst] [A] [B] [C] [D] _ _ _ _.

