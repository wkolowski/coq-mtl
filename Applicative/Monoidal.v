Add LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

(* An altenrative characterization of applicative functors as lax monoidal
   functors. *)

Definition par {A A' B B' : Type} (f : A -> A') (g : B -> B')
  : A * B -> A' * B' := fun '(a, b) => (f a, g b).

Notation "f *** g" := (par f g) (at level 40).

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
        fmap (fun '((a, b), c) => (a, (b, c))) (pairF (pairF a b) c) =
        pairF a (pairF b c);
    natural :
      forall (A A' B B' : Type) (f : A -> A') (g : B -> B')
      (a : F A) (b : F B),
        fmap (f *** g) (pairF a b) = pairF (fmap f a) (fmap g b)
}.

Hint Rewrite @pairF_default_l @pairF_default_r @pairF_assoc : monoidal.

Require Import HSLib.Applicative.Applicative.

Definition ret_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A : Type} (x : A) : F A :=
    fmap (fun u : unit => x) default.

Definition ap_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A B : Type}
  (f : F (A -> B)) (a : F A) : F B :=
    fmap (fun '(f, a) => f a) (pairF f a).

Instance isMonoidal_Applicative (F : Type -> Type) (inst : isMonoidal F)
  : Applicative F :=
{
    is_functor := @isMonoidal_functor F inst;
    ret := @ret_isMonoidal F inst;
    ap := @ap_isMonoidal F inst
}.
Proof.
  all: unfold ret_isMonoidal, ap_isMonoidal; intros.
    rewrite <- pairF_default_l, <- pairF_default_r.
Abort.