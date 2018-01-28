Add LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Control.Functor.

Class Applicative (F : Type -> Type) : Type :=
{
    is_functor :> Functor F;
    pure : forall {A : Type}, A -> F A;
    ap : forall {A B : Type}, F (A -> B) -> F A -> F B;
    identity :
      forall (A : Type) (ax : F A),
        ap (pure id) ax = ax;
    composition :
      forall (A B C : Type) (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
        ap (ap (ap (pure compose) ag) af) ax = ap ag (ap af ax);
    homomorphism :
      forall (A B : Type) (f : A -> B) (x : A),
        ap (pure f) (pure x) = pure (f x);
    interchange :
      forall (A B : Type) (f : F (A -> B)) (x : A),
        ap f (pure x) = ap (pure (fun f => f x)) f;
(*    fmap_pure_ap :
      forall (A B : Type) (f : A -> B) (x : F A),
        ap (pure f) x = fmap f x*)
}.

Coercion is_functor : Applicative >-> Functor.

(* TODO: check if the last law is necessary *)

CoInductive Stream (A : Type) : Type :=
    | snil : Stream A
    | scons : A -> Stream A -> Stream A .

Arguments snil {A}.
Arguments scons {A} _ _.

CoFixpoint fmap_Stream
  {A B : Type} (f : A -> B) (sa : Stream A) : Stream B :=
match sa with
    | snil => snil
    | scons h t => scons (f h) (fmap_Stream f t)
end.

Instance Functor_Stream : Functor Stream :=
{
    fmap := @fmap_Stream
}.
Proof.
  intro. ext s.
Abort. 

(*Definition ap'_List :
  {A B : Type} (lf : list (A -> B)) (la : list A) : list B :=
*)



(* TODO: *) Section ApplicativeLaws.

Variables
  (F : Type -> Type)
  (inst : Applicative F).

Goal
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : F A),
    ap (pure (f .> g)) x = ap (pure g) (ap (pure f) x).
Proof.
  intros.
  replace (ap (pure (f .> g)) x)
  with (ap (ap (ap (pure compose) (pure g)) (pure f)) x).
    rewrite composition. reflexivity.
    rewrite composition.
Abort.


Definition identity' : Prop :=
  forall (A : Type) (ax : F A),
    ap (pure id) ax = ax.

Definition composition' : Prop :=
  forall (A B C : Type) (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
    ap (ap (ap (pure compose) ag) af) ax = ap ag (ap af ax).

Definition homomorphism' : Prop :=
  forall (A B : Type) (f : A -> B) (x : A),
    ap (pure f) (pure x) = pure (f x).

Definition interchange' : Prop :=
  forall (A B : Type) (f : F (A -> B)) (x : A),
    ap f (pure x) = ap (pure (fun f => f x)) f.

Definition fmap_pure_ap' : Prop :=
  forall (A B : Type) (f : A -> B) (x : F A),
    fmap f x = ap (pure f) x.

Goal
  fmap_pure_ap' -> identity'.
Proof.
  unfold fmap_pure_ap', identity'. intros.
  rewrite <- H. functor.
Qed.

Goal
  fmap_pure_ap' -> homomorphism'.
Proof.
  unfold fmap_pure_ap', homomorphism'.
  intros. rewrite <- H.
Abort.
End ApplicativeLaws.