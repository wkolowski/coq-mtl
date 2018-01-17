Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Class Functor (F : Type -> Type) : Type :=
{
    fmap : forall {A B : Type}, (A -> B) -> (F A -> F B);
    fmap_pres_id :
      forall (A : Type), fmap (@id A) = id;
    fmap_pres_comp :
      forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap (f .> g) = fmap f .> fmap g
}.

Section DerivedLaws.

Variables
  (F : Type -> Type)
  (inst : Functor F).

Lemma fmap_pres_comp' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : F A),
    fmap (f .> g) x = fmap g (fmap f x).
Proof.
  intros. rewrite fmap_pres_comp. unfold compose. reflexivity.
Qed.

End DerivedLaws.

Hint Rewrite @fmap_pres_id @fmap_pres_comp @fmap_pres_comp' : functor.
Hint Rewrite @fmap_pres_id : functor'.
Hint Rewrite <- @fmap_pres_comp @fmap_pres_comp' : functor'.

Ltac functor_simpl :=
  autorewrite with functor.

Ltac functor_simpl' :=
  autorewrite with functor'.

Ltac functor :=
  intros; (functor_simpl + functor_simpl'); id;
  (congruence + reflexivity).

Section FunctorFuns.

Variable F : Type -> Type.
Variable inst : Functor F.
Variables A : Type.

Definition void (ma : F A) : F unit :=
  fmap (fun _ => tt) ma.

End FunctorFuns.

Arguments void [F] [inst] [A] _.