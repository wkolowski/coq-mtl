Require Export HSLib.Control.Applicative.
Require Export HSLib.Theory.Monoidal.

Definition pure_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A : Type} (x : A) : F A :=
    fmap (fun u : unit => x) default.

Definition ap_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A B : Type}
  (f : F (A -> B)) (a : F A) : F B :=
    fmap (fun p => apply (fst p) (snd p)) (pairF f a).

Lemma wutzor_snd :
  forall {W A B C : Type} (f : B -> C) (g : A -> B),
    ((fun _ : W => f) *** g) .>
    (fun p : (B -> C) * B => apply (fst p) (snd p)) = snd .> g .> f.
Proof.
  intros. unfold compose, par. ext x. destruct x. cbn. reflexivity.
Qed.

Ltac monoidal := repeat (
multimatch goal with
    | |- ?x =?x => reflexivity
    | |- context [fmap snd (pairF _ _)] => rewrite pairF_default_l
    | |- context [fmap fst (pairF _ _)] => rewrite pairF_default_r
    | |- context [fmap id _] => rewrite !fmap_id
    | |- context [id _] => rewrite !id_eq
    | |- context [id .> _] => rewrite !id_left
    | |- context [_ .> id] => rewrite !id_right
    | |- context [fmap (fst .> _)] => rewrite !fmap_comp'
    | |- context [fmap (snd .> _)] => rewrite !fmap_comp'
    | _ => rewrite ?wutzor_snd
    | |- context [pairF (fmap ?f ?a) ?x] =>
          replace x with (fmap id x) by functor;
          rewrite <- ?natural, <- ?fmap_comp', ?fmap_id
    | |- context [pairF ?x (fmap ?f ?a)] =>
            replace x with (fmap id x) by functor;
            rewrite <- ?natural, <- ?fmap_comp', ?fmap_id
end).

Instance isMonoidal_Applicative (F : Type -> Type) (inst : isMonoidal F)
  : Applicative F :=
{
    is_functor := @isMonoidal_functor F inst;
    pure := @pure_isMonoidal F inst;
    ap := @ap_isMonoidal F inst
}.
Proof.
  all: unfold pure_isMonoidal, ap_isMonoidal; intros; monoidal.
    rewrite !par_comp. cbn. unfold apply.
      rewrite <- (pairF_default_l _ (pairF ag (pairF af ax))).
      rewrite <- ?pairF_assoc, <- ?fmap_comp'. repeat f_equal.
      ext p. destruct p as [[[u g] f] x]. cbn. reflexivity.
    rewrite <- fmap_comp'. reflexivity.
    rewrite <- fmap_comp', par_comp. cbn.
      replace (fun p : (A -> B) * unit => id (fst p) x)
      with (@fst (A -> B) unit .> flip apply x).
        monoidal. unfold flip, apply, id, compose. reflexivity.
        ext p. destruct p. cbn. reflexivity.
Qed.

Definition default_Applicative
  {F : Type -> Type} {inst : Applicative F} : F unit := pure tt.

Definition pairF_Applicative
  {F : Type -> Type} {inst : Applicative F} {A B : Type}
  (x : F A) (y : F B) : F (A * B)%type := pair <$> x <*> y.

Hint Unfold default_Applicative pairF_Applicative compose (* WUT *): HSLib.

Hint Rewrite @identity @interchange @homomorphism @fmap_pure_ap
  : HSLib'.
Hint Rewrite <- @composition
  : HSLib'.

Instance Applicative_isMonoidal
  (F : Type -> Type) (inst : Applicative F) : isMonoidal F :=
{
    isMonoidal_functor := inst;
    default := default_Applicative;
    pairF := @pairF_Applicative F inst;
}.
Proof.
  all: hs; repeat (rewrite <- composition, homomorphism);
  autorewrite with HSLib'; reflexivity.
Defined.