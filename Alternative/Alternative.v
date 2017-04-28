Require Import Applicative.
Require Import ApplicativeInst.

Class Alternative (F : Type -> Type) : Type :=
{
    is_applicative :> Applicative F;
    aempty : forall {A : Type}, F A;
    aplus : forall {A : Type}, F A -> F A -> F A;
    id_left : forall (A : Type) (fa : F A),
        aplus aempty fa = fa;
    id_right : forall (A : Type) (fa : F A),
        aplus fa aempty = fa;
    aplus_assoc : forall (A : Type) (x y z : F A),
        aplus x (aplus y z) = aplus (aplus x y) z
}.