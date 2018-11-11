Require Export HSLib.Base.

Axiom
  (F : Type -> Type)
  (fmap : forall {A B : Type}, (A -> B) -> F A -> F B)
  (pure : forall {A : Type}, A -> F A)
  (ap : forall {A B : Type}, F (A -> B) -> F A -> F B).

Notation "f <*> x" := (ap f x)
  (left associativity, at level 40).

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

Definition ap_pure_fmap : Prop :=
  forall (A B : Type) (f : A -> B) (x : F A),
    fmap f x = ap (pure f) x.

Definition fmap_pure : Prop :=
  forall (A B : Type) (f : A -> B) (x : A),
    fmap f (pure x) = pure (f x).

Lemma identity' :
  ap_pure_fmap -> fmap_id -> identity.
Proof.
  compute. intros ap_pure_fmap fmap_id A x.
  rewrite <- ap_pure_fmap, fmap_id. reflexivity.
Qed.

Lemma fmap_pure' :
  ap_pure_fmap -> homomorphism -> fmap_pure.
Proof.
  compute. intros ap_pure_fmap homomorphism A B f x.
  rewrite ap_pure_fmap, homomorphism. reflexivity.
Qed.

Lemma homomorphism' :
  fmap_pure -> ap_pure_fmap -> homomorphism.
Proof.
  compute. intros fmap_pure ap_pure_fmap A B f x.
  rewrite <- ap_pure_fmap, fmap_pure. reflexivity.
Qed.

Lemma ap_pure_fmap' :
  fmap_pure -> identity -> ap_pure_fmap.
Proof.
  compute. intros fmap_pure identity A B f x.
Abort.