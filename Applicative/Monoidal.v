Add LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

(* An altenrative characterization of applicative functors as lax monoidal
   functors. *)

Lemma id_eq :
  forall (A : Type) (x : A), id x = x.
Proof. reflexivity. Qed.

Definition par {A A' B B' : Type} (f : A -> B) (g : A' -> B')
  : A * A' -> B * B' := fun '(a, b) => (f a, g b).

Notation "f *** g" := (par f g) (at level 40).

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

Definition reassoc {A B C : Type} : (A * B) * C -> A * (B * C) :=
  fun '((a, b), c) => (a, (b, c)).

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

Require Import HSLib.Applicative.Applicative.

Definition ret_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A : Type} (x : A) : F A :=
    fmap (fun u : unit => x) default.

Definition ap_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A B : Type}
  (f : F (A -> B)) (a : F A) : F B :=
    fmap (fun p => apply (fst p) (snd p)) (pairF f a).

Hint Rewrite @fmap_pres_id @fmap_pres_comp @fmap_pres_comp' : functor.

Ltac functor :=
  repeat (cbn; unfold id, compose, par; intros;
       autorewrite with functor; try congruence); fail.

Lemma wutzor_snd :
  forall {W A B C : Type} (f : B -> C) (g : A -> B),
    ((fun _ : W => f) *** g) .>
    (fun p : (B -> C) * B => apply (fst p) (snd p)) = snd .> g .> f.
Proof.
  intros. unfold compose, par. ext x. destruct x. cbn. reflexivity.
Qed.

Ltac woed := repeat (
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
    woed.
    woed. rewrite !par_wut. cbn. unfold apply. admit.
    woed. rewrite <- fmap_pres_comp'. unfold compose. reflexivity.
    woed.
      rewrite <- fmap_pres_comp', par_wut. cbn.
      replace (fun p : (A -> B) * unit => id (fst p) x)
      with (@fst (A -> B) unit .> flip apply x).
        Focus 2. ext p. destruct p. cbn. reflexivity.
        woed. unfold flip, apply, id, compose. reflexivity.
    woed.
Admitted.

Definition default_Applicative
  {F : Type -> Type} {inst : Applicative F} : F unit := ret tt.

Definition pairF_Applicative
  {F : Type -> Type} {inst : Applicative F} {A B : Type}
  (x : F A) (y : F B) : F (A * B)%type := pair <$> x <*> y.

Hint Rewrite @identity @interchange @homomorphism @fmap_ret_ap
  : applicative_laws2.
Hint Rewrite <- @composition
  : applicative_laws2.

Ltac applicative2 :=
  intros; autorewrite with applicative_laws2; try congruence.

Instance Applicative_isMonoidal
  (F : Type -> Type) (inst : Applicative F) : isMonoidal F :=
{
    isMonoidal_functor := inst;
    default := default_Applicative;
    pairF := @pairF_Applicative F inst;
}.
Proof.
  all: unfold default_Applicative, pairF_Applicative; applicative.
    applicative2.
    applicative2.
    repeat (rewrite <- composition, homomorphism). applicative2.
      unfold compose. reflexivity.
    applicative2. unfold compose, par. reflexivity.
Defined.