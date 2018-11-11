Require Import Applicative_minimal.

Definition M := F.

Axiom
  (bind : forall {A B : Type}, M A -> (A -> M B) -> M B).

Definition bind_pure_l : Prop :=
  forall (A B : Type) (f : A -> M B) (a : A),
    bind (pure a) f = f a.

Definition bind_pure_r : Prop :=
  forall (A : Type) (ma : M A), bind ma pure = ma.

Definition bind_assoc : Prop :=
  forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
    bind (bind ma f) g = bind ma (fun x => bind (f x) g).

Definition bind_ap : Prop :=
  forall (A B : Type) (mf : M (A -> B)) (mx : M A),
    mf <*> mx = bind mf (fun f => bind mx (fun x => pure (f x))).

Notation "mx >>= f" := (bind mx f) (at level 40).

(*
Lemma bind_pure_l' :
  forall (A B : Type) (f : A -> M B) (a : A),
    pure a >>= f = f a.
Proof.
  intros.
  replace (pure a >>= f)
  with ((pure f >>= fun f' => pure a >>= fun a => pure (f' a)) >>= id).
    rewrite <- bind_ap. Check identity. rewrite homomorphism.
      admit.
    rewrite <- bind_ap. rewrite homomorphism. admit.
Admitted.
*)

Lemma fmap_bind_pure :
  ap_pure_fmap -> bind_ap -> bind_pure_l ->
    forall (A B : Type) (f : A -> B) (x : M A),
      fmap f x = x >>= (fun a : A => pure (f a)).
Proof.
  unfold ap_pure_fmap, bind_ap, bind_pure_l.
  intros ap_pure_fmap bind_ap bind_pure_l A B f x.
  replace (x >>= fun a : A => pure (f a))
  with (pure f >>= fun f => x >>= fun a => pure (f a)).
    rewrite <- bind_ap, ap_pure_fmap. reflexivity.
    rewrite bind_pure_l. reflexivity.
Qed.

Lemma bind_pure_r' :
  fmap_id -> ap_pure_fmap -> bind_ap -> bind_pure_l ->
    bind_pure_r.
Proof.
  unfold fmap_id, ap_pure_fmap, bind_ap, bind_pure_l, bind_pure_r.
  intros fmap_id ap_pure_fmap bind_ap bind_pure_l A ma.
  change pure with (fun x : A => pure (id x)).
  rewrite <- fmap_bind_pure; auto. rewrite fmap_id. reflexivity.
Qed.