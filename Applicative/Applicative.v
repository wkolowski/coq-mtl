Add LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Class Applicative (F : Type -> Type) : Type :=
{
    is_functor :> Functor F;
    ret : forall {A : Type}, A -> F A;
    ap : forall {A B : Type}, F (A -> B) -> F A -> F B;
    identity :
      forall (A : Type) (ax : F A),
        ap (ret id) ax = ax;
    composition :
      forall (A B C : Type) (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
        ap (ap (ap (ret compose) ag) af) ax = ap ag (ap af ax);
    homomorphism :
      forall (A B : Type) (f : A -> B) (x : A),
        ap (ret f) (ret x) = ret (f x);
    interchange :
      forall (A B : Type) (f : F (A -> B)) (x : A),
        ap f (ret x) = ap (ret (fun f => f x)) f;
    fmap_pure_ap :
      forall (A B : Type) (f : A -> B) (x : F A),
        fmap f x = ap (ret f) x
}.

Coercion is_functor : Applicative >-> Functor.

Module ApplicativeNotations.

Notation "f $$ x" := (ap f x)
  (left associativity, at level 40, only parsing).

Notation "f <*> x" := (ap f x)
  (left associativity, at level 40).

Notation "f <$> x" := (fmap f x)
  (left associativity, at level 40, only parsing).

Definition constlA
  {F : Type -> Type} {inst : Applicative F} {A B : Type} (a : F A) (b : F B)
    : F A := const <$> a <*> b.

Definition constrA
  {F : Type -> Type} {inst : Applicative F} {A B : Type} (a : F A) (b : F B)
    : F B := (const .> fmap) id a <*> b.

Notation "a <* b" := (constlA a b)
  (right associativity, at level 42).

Notation "a *> b" := (constrA a b)
  (right associativity, at level 42).

End ApplicativeNotations.

Export ApplicativeNotations.

Section ApplicativeFuns.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D E : Type.

Definition liftA2
  (f : A -> B -> C) (fa : F A) (fb : F B) : F C :=
    ret f <*> fa <*> fb.

Definition liftA3
  (f : A -> B -> C -> D) (fa : F A) (fb : F B) (fc : F C) : F D :=
    ret f <*> fa <*> fb <*> fc.

Definition liftA4
  (f : A -> B -> C -> D -> E) (fa : F A) (fb : F B) (fc : F C) (fd : F D)
    : F E := ret f <*> fa <*> fb <*> fc <*> fd.

End ApplicativeFuns.

Arguments liftA2 [F inst A B C] _ _ _.
Arguments liftA3 [F inst A B C D ] _ _ _ _.
Arguments liftA4 [F inst A B C D E] _ _ _ _ _.

Section ApplicativeFuns2.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D : Type.

Fixpoint filterA (p : A -> F bool) (la : list A) : F (list A) :=
match la with
    | [] => ret []
    | h :: t =>
        let f :=
          fmap (fun b : bool => if b then (cons h) else id) (p h)
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