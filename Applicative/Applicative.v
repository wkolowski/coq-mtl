Add LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Class Applicative (F : Type -> Type) : Type :=
{
    is_functor :> Functor F;
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

Coercion is_functor : Applicative >-> Functor.

Section ApplicativeFuns.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D : Type.

Definition liftA (f : A -> B) (fa : F A)
    : F B := ap (ret f) fa.
Definition liftA2 (f : A -> B -> C) (fa : F A) (fb : F B)
    : F C := ap (ap (ret f) fa) fb.
Definition liftA3 (f : A -> B -> C -> D) (fa : F A) (fb : F B) (fc : F C)
    : F D := ap (ap (ap (ret f) fa) fb) fc.

End ApplicativeFuns.

Arguments liftA [F] [inst] [A] [B] _ _.
Arguments liftA2 [F] [inst] [A] [B] [C] _ _ _.
Arguments liftA3 [F] [inst] [A] [B] [C] [D] _ _ _ _.

Section ApplicativeFuns2.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D : Type.

Fixpoint filterA (p : A -> F bool) (la : list A) : F (list A) :=
match la with
    | [] => ret []
    | h :: t =>
        let f :=
            liftA (fun b : bool => if b then (cons h) else id) (p h)
        in ap f (filterA p t)
end.

Fixpoint zipWithA (f : A -> B -> F C) (la : list A) (lb : list B)
    : F (list C) :=
match la, lb with
    | [], _ => ret []
    | _, [] => ret []
    | ha :: ta, hb :: tb =>
        liftA2 (@cons C) (f ha hb) (zipWithA f ta tb)
end.

Fixpoint replicateA (n : nat) (x : F A) : F (list A) :=
match n with
    | 0 => ret []
    | S n' => liftA2 (@cons A) x (replicateA n' x)
end.

Definition when (cond : bool) (a : F unit) : F unit :=
    if cond then a else ret tt.

Definition unless (cond : bool) (a : F unit) : F unit :=
    if cond then ret tt else a.

End ApplicativeFuns2.