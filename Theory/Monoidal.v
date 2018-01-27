Add LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Control.Functor.

(* Auxiliary functions needed to define Monoidal. *)
Definition reassoc {A B C : Type} : (A * B) * C -> A * (B * C) :=
  fun '((a, b), c) => (a, (b, c)).

Definition par {A A' B B' : Type} (f : A -> B) (g : A' -> B')
  : A * A' -> B * B' := fun '(a, b) => (f a, g b).

Notation "f *** g" := (par f g) (at level 40).

(* An alternative characterization of applicative functors as lax monoidal
   functors (or rather, strong monoidal functors, because in the category
   of Coq's types and functions all monoidal functors are strong. *)
Class isMonoidal (F : Type -> Type) : Type :=
{
    isMonoidal_functor :> Functor F;
    default : F unit;
    pairF : forall {A B : Type}, F A -> F B -> F (A * B)%type;
    pairF_default_l :
      forall (A : Type) (v : F A),
        fmap snd (pairF default v) = v;
    pairF_default_r :
      forall (A : Type) (v : F A),
        fmap fst (pairF v default) = v;
    pairF_assoc :
      forall (A B C : Type) (a : F A) (b : F B) (c : F C),
        fmap reassoc (pairF (pairF a b) c) =
        pairF a (pairF b c);
    natural :
      forall (A A' B B' : Type) (f : A -> A') (g : B -> B')
      (a : F A) (b : F B),
        fmap (f *** g) (pairF a b) = pairF (fmap f a) (fmap g b)
}.

Hint Rewrite @pairF_default_l @pairF_default_r @pairF_assoc : monoidal.