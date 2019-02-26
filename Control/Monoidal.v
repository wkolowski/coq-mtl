Require Export HSLib.Control.Functor.

(* Auxiliary functions needed to define Monoidal. *)
Definition reassoc
  {A B C : Type} : (A * B) * C -> A * (B * C) :=
    fun '((a, b), c) => (a, (b, c)).

Definition par
  {A A' B B' : Type} (f : A -> B) (g : A' -> B') : A * A' -> B * B' :=
    fun '(a, b) => (f a, g b).

Notation "f *** g" := (par f g) (at level 40).

(** An alternative characterization of applicative functors as lax monoidal
    functors (or rather, strong monoidal functors, because in the category
    of Coq's types and functions all monoidal functors are strong. *)
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

Lemma par_id :
  forall (A B : Type), @id A *** @id B = id.
Proof.
  intros. unfold par, id. ext p. destruct p. reflexivity.
Qed.

Lemma comp_par_par :
  forall (A B C A' B' C' : Type)
  (f1 : A -> B) (f2 : B -> C) (g1 : A' -> B') (g2 : B' -> C'),
    (f1 *** g1) .> (f2 *** g2) = (f1 .> f2) *** (g1 .> g2).
Proof.
  intros. unfold compose, par. ext p. destruct p. reflexivity.
Qed.

Lemma par_comp :
  forall (A B A' B' X : Type) (f : A -> B) (g : A' -> B') (h : B * B' -> X),
    (f *** g) .> h = fun p : A * A' => h (f (fst p), g (snd p)).
Proof.
  intros. unfold compose, par. ext p. destruct p. cbn. reflexivity.
Qed.

Lemma aux :
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
    | _ => rewrite ?aux
    | |- context [pairF (fmap ?f ?a) ?x] =>
          replace x with (fmap id x) by hs;
          rewrite <- ?natural, <- ?fmap_comp', ?fmap_id
    | |- context [pairF ?x (fmap ?f ?a)] =>
            replace x with (fmap id x) by hs;
            rewrite <- ?natural, <- ?fmap_comp', ?fmap_id
end).