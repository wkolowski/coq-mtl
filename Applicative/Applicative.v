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
    fmap_ret_ap :
      forall (A B : Type) (f : A -> B) (x : F A),
        fmap f x = ap (ret f) x;
}.
(* TODO: sprawdzić czy ostatnie prawo jest potrzbne. *)

Coercion is_functor : Applicative >-> Functor.

Hint Rewrite @identity @composition @homomorphism @fmap_ret_ap
  : applicative_laws.
Hint Rewrite <- @interchange
  : applicative_laws.

Ltac applicative :=
  intros; autorewrite with applicative_laws; try congruence.

(* TODO: wut applicative laws *)
Section wut.

Variables
  (F : Type -> Type)
  (inst : Applicative F).

Goal
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : F A),
    ap (ret (f .> g)) x = ap (ret g) (ap (ret f) x).
Proof.
  intros.
  replace (ap (ret (f .> g)) x)
  with (ap (ap (ap (ret compose) (ret g)) (ret f)) x).
    rewrite composition. reflexivity.
    rewrite composition.
Abort.

Lemma fmap_ret :
  forall (F : Type -> Type) (inst : Applicative F)
  (A B : Type) (f : A -> B) (x : A),
    fmap f (ret x) = ret (f x).
Proof.
  intros. rewrite fmap_ret_ap. rewrite homomorphism. reflexivity.
Qed.

Definition identity' : Prop :=
  forall (A : Type) (ax : F A),
    ap (ret id) ax = ax.

Definition composition' : Prop :=
  forall (A B C : Type) (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
    ap (ap (ap (ret compose) ag) af) ax = ap ag (ap af ax).

Definition homomorphism' : Prop :=
  forall (A B : Type) (f : A -> B) (x : A),
    ap (ret f) (ret x) = ret (f x).

Definition interchange' : Prop :=
  forall (A B : Type) (f : F (A -> B)) (x : A),
    ap f (ret x) = ap (ret (fun f => f x)) f.

Definition fmap_ret_ap' : Prop :=
  forall (A B : Type) (f : A -> B) (x : F A),
    fmap f x = ap (ret f) x.

Goal
  fmap_ret_ap' -> identity'.
Proof.
  unfold fmap_ret_ap', identity'. intros.
  rewrite <- H. functor.
Qed.

Goal
  fmap_ret_ap' -> homomorphism'.
Proof.
  unfold fmap_ret_ap', homomorphism'.
  intros. rewrite <- H. Print Functor. 
Abort.

End wut. (* TODO *)

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

Section Lifts.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D E : Type.

Definition liftA2
  (f : A -> B -> C)
  (fa : F A) (fb : F B) : F C :=
    ret f <*> fa <*> fb.

Definition liftA3
  (f : A -> B -> C -> D)
  (fa : F A) (fb : F B) (fc : F C) : F D :=
    ret f <*> fa <*> fb <*> fc.

Definition liftA4
  (f : A -> B -> C -> D -> E)
  (fa : F A) (fb : F B) (fc : F C) (fd : F D) : F E :=
    ret f <*> fa <*> fb <*> fc <*> fd.

End Lifts.

Arguments liftA2 [F inst A B C] _ _ _.
Arguments liftA3 [F inst A B C D ] _ _ _ _.
Arguments liftA4 [F inst A B C D E] _ _ _ _ _.

Section ApplicativeFuns1.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D : Type.

Fixpoint filterA (p : A -> F bool) (la : list A) : F (list A) :=
match la with
    | [] => ret []
    | h :: t =>
        let f :=
          fmap (fun b : bool => if b then (cons h) else id) (p h)
        in f <*> filterA p t
end.

Fixpoint sequenceA (lma : list (F A)) : F (list A) :=
match lma with
    | [] => ret []
    | h :: t => cons <$> h <*> sequenceA t
end.

Fixpoint replicateA (n : nat) (x : F A) : F (list A) :=
match n with
    | 0 => ret []
    | S n' => cons <$> x <*> replicateA n' x
end.

Fixpoint zipWithA (f : A -> B -> F C) (la : list A) (lb : list B)
    : F (list C) :=
match la, lb with
    | [], _ => ret []
    | _, [] => ret []
    | ha :: ta, hb :: tb =>
        cons <$> f ha hb <*> zipWithA f ta tb
end.

Definition when (cond : bool) (a : F unit) : F unit :=
  if cond then a else ret tt.

Definition unless (cond : bool) (a : F unit) : F unit :=
  if cond then ret tt else a.

End ApplicativeFuns1.

Arguments filterA [F inst A] _ _.
Arguments sequenceA [F inst A] _.
Arguments replicateA [F inst A] _ _.
Arguments zipWithA [F inst A B C] _ _ _.
Arguments when [F inst] _ _.
Arguments unless [F inst] _ _.

Section ApplicativeFuns2.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D E : Type.

Definition mapA (f : A -> F B) (la : list A) : F (list B) :=
  sequenceA (map f la).

Definition forA (la : list A) (f : A -> F B) : F (list B) :=
  mapA f la.

End ApplicativeFuns2.