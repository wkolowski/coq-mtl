Require Export Base.

(** This module aims to check whether [Applicative]'s laws are orthogonal,
    i.e. independent from each other. We take an axiomatic approach.

    First we postulate the existence of a thing [F] that has some functions
    named [fmap], [pure] and [ap]. *)

Axiom
  (F : Type -> Type)
  (fmap : forall {A B : Type}, (A -> B) -> F A -> F B)
  (pure : forall {A : Type}, A -> F A)
  (ap : forall {A B : Type}, F (A -> B) -> F A -> F B).

(** We introduce familiar notations. *)

Notation "f <*> x" := (ap f x)
  (left associativity, at level 40).

(** Then we define various laws that this [F] can possibly satisfy. *)

Definition fmap_id : Prop :=
  forall A : Type, fmap (@id A) = id.

Definition fmap_comp : Prop :=
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    fmap (f .> g) = fmap f .> fmap g.

Definition identity : Prop :=
  forall (A : Type) (ax : F A), ap (pure id) ax = ax.

Definition composition : Prop :=
  forall (A B C : Type) (af : F (A -> B)) (ag : F (B  -> C)) (ax : F A),
    ap (ap (ap (pure compose) ag) af) ax = ap ag (ap af ax).

Definition homomorphism : Prop :=
  forall (A B : Type) (f : A -> B) (x : A),
    ap (pure f) (pure x) = pure (f x).

Definition interchange : Prop :=
  forall (A B : Type) (f : F (A -> B)) (x : A),
    ap f (pure x) = ap (pure (fun f => f x)) f.

Definition fmap_pure_ap : Prop :=
  forall (A B : Type) (f : A -> B) (x : F A),
    fmap f x = ap (pure f) x.

(** This law is some kind of alternative for [fmap_pure_ap]. *)
Definition fmap_pure : Prop :=
  forall (A B : Type) (f : A -> B) (x : A),
    fmap f (pure x) = pure (f x).

(** Finally we try to derive some of these laws from others. It turns out
    that [identity] follows from [fmap_pure_ap] and the functor laws. *)

Lemma identity' :
  fmap_pure_ap -> fmap_id -> identity.
Proof.
  compute. intros fmap_pure_ap fmap_id A x.
  rewrite <- fmap_pure_ap, fmap_id. reflexivity.
Qed.

Lemma homomorphism' :
  fmap_pure_ap -> fmap_pure -> homomorphism.
Proof.
  compute. intros fmap_pure_ap fmap_pure A B f x.
  rewrite <- fmap_pure_ap, fmap_pure. reflexivity.
Qed.

Lemma fmap_id' :
  fmap_pure_ap -> identity -> fmap_id.
Proof.
  compute. intros fmap_pure_ap identity A.
  ext a. rewrite fmap_pure_ap, identity.
  reflexivity.
Qed.

Lemma fmap_pure' :
  fmap_pure_ap -> homomorphism -> fmap_pure.
Proof.
  compute. intros fmap_pure_ap homomorphism A B f x.
  rewrite fmap_pure_ap, homomorphism. reflexivity.
Qed.