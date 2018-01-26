Add LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Control.Applicative.
Require Export HSLib.Control.Monoidal.

Lemma par_id :
  forall (A B : Type), @id A *** @id B = id.
Proof.
  intros. unfold par, id. ext p. destruct p. reflexivity.
Qed.

Lemma par_comp :
  forall (A B C A' B' C' : Type)
  (f1 : A -> B) (f2 : B -> C) (g1 : A' -> B') (g2 : B' -> C'),
    (f1 *** g1) .> (f2 *** g2) = (f1 .> f2) *** (g1 .> g2).
Proof.
  intros. unfold compose, par. ext p. destruct p. reflexivity.
Qed.

Lemma par_wut :
  forall (A B A' B' X : Type) (f : A -> B) (g : A' -> B') (h : B * B' -> X),
    (f *** g) .> h = fun p : A * A' => h (f (fst p), g (snd p)).
Proof.
  intros. unfold compose, par. ext p. destruct p. cbn. reflexivity.
Qed.

Definition ret_isMonoidal
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
    | |- context [fmap id _] => rewrite !fmap_pres_id
    | |- context [id _] => rewrite !id_eq
    | |- context [id .> _] => rewrite !id_left
    | |- context [_ .> id] => rewrite !id_right
    | |- context [fmap (fst .> _)] => rewrite !fmap_pres_comp'
    | |- context [fmap (snd .> _)] => rewrite !fmap_pres_comp'
    | _ => rewrite ?wutzor_snd
    | |- context [pairF (fmap ?f ?a) ?x] =>
          replace x with (fmap id x) by functor;
          rewrite <- ?natural, <- ?fmap_pres_comp', ?fmap_pres_id
    | |- context [pairF ?x (fmap ?f ?a)] =>
            replace x with (fmap id x) by functor;
            rewrite <- ?natural, <- ?fmap_pres_comp', ?fmap_pres_id
end).

Instance isMonoidal_Applicative (F : Type -> Type) (inst : isMonoidal F)
  : Applicative F :=
{
    is_functor := @isMonoidal_functor F inst;
    ret := @ret_isMonoidal F inst;
    ap := @ap_isMonoidal F inst
}.
Proof.
  all: unfold ret_isMonoidal, ap_isMonoidal; intros.
    (*replace ax with (fmap id ax) by functor.
    rewrite <- natural. rewrite <- fmap_pres_comp'.
    unfold compose, par, apply. cbn.
    replace
    (fun x : unit * A =>
   fst (let '(_, b) := x in (id, id b))
     (snd (let '(_, b) := x in (id, id b))))
    with
    (@snd unit A).
       Focus 2. ext p. destruct p. cbn. reflexivity.
       rewrite pairF_default_l. rewrite fmap_pres_id. reflexivity.*)
    monoidal.
    monoidal. rewrite !par_wut. cbn. unfold apply. admit.
    monoidal. functor.
    monoidal.
      rewrite <- fmap_pres_comp', par_wut. cbn.
      replace (fun p : (A -> B) * unit => id (fst p) x)
      with (@fst (A -> B) unit .> flip apply x).
        Focus 2. ext p. destruct p. cbn. reflexivity.
        monoidal. unfold flip, apply, id, compose. reflexivity.
    monoidal.
Admitted.

Definition default_Applicative
  {F : Type -> Type} {inst : Applicative F} : F unit := ret tt.

Definition pairF_Applicative
  {F : Type -> Type} {inst : Applicative F} {A B : Type}
  (x : F A) (y : F B) : F (A * B)%type := pair <$> x <*> y.

Hint Unfold default_Applicative pairF_Applicative compose (* WUT *): HSLib.

Hint Rewrite @identity @interchange @homomorphism @fmap_ret_ap
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