Require Import Base.

Class Functor (F : Type -> Type) : Type :=
{
    fmap : forall {A B : Type}, (A -> B) -> (F A -> F B);
    fmap_pres_id : forall (A : Type), fmap (@id A) = id;
    fmap_pres_comp : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap (f .> g) = fmap f .> fmap g
}.

Set Implicit Arguments.

Section ops.

Variable F : Type -> Type.
Variable inst : Functor F.

Definition void {A : Type} (ma : F A) : F unit :=
    fmap (fun _ => tt) ma.

End ops.

Arguments void [F] [inst] [A] _.
