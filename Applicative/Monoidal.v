Add LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

(* An altenrative characterization of applicative functors as lax monoidal
   functors. *)

Definition par {A A' B B' : Type} (f : A -> A') (g : B -> B')
  : A * B -> A' * B' := fun '(a, b) => (f a, g b).

Notation "f *** g" := (par f g) (at level 40).

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
        fmap (fun '((a, b), c) => (a, (b, c))) (pairF (pairF a b) c) =
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
    (*fmap (fun '(f, a) => f a) (pairF f a).*)
    fmap (fun p => apply (fst p) (snd p)) (pairF f a).

Hint Rewrite @fmap_pres_id @fmap_pres_comp @fmap_pres_comp' : functor.

Ltac functor :=
  repeat (cbn; unfold id, compose, par; intros;
       autorewrite with functor; try congruence); fail.

Ltac aux :=
    match goal with
        | |- context [pairF (fmap _ _) ?x] =>
            replace x with (fmap id x) by functor;
            rewrite <- ?natural, <- ?fmap_pres_comp';
            unfold id, compose, par
    end.

Instance isMonoidal_Applicative (F : Type -> Type) (inst : isMonoidal F)
  : Applicative F :=
{
    is_functor := @isMonoidal_functor F inst;
    ret := @ret_isMonoidal F inst;
    ap := @ap_isMonoidal F inst
}.
Proof.
  all: unfold ret_isMonoidal, ap_isMonoidal; intros.
  
(*
    aux.
    replace
      (fun x : unit * A =>
       let '(f, a) := let '(_, b) := x in (fun x0 : A => x0, b) in f a)
    with (@snd unit A).
      Focus 2. ext p. destruct p. cbn. reflexivity.
      rewrite pairF_default_l. rewrite fmap_pres_id. reflexivity.
    Focus 4. aux.
      replace
    (fun x0 : unit * A => let '(f0, a) := let '(_, b) := x0 in (f, b) in f0 a)
      with (@snd unit A .> f).
      Focus 2. unfold compose. ext p. destruct p. cbn. reflexivity.
      rewrite fmap_pres_comp'. rewrite pairF_default_l. reflexivity.
    Focus 3. aux.
        replace
          (fun x0 : (A -> B) * unit =>
           let '(f0, a) := let '(a, _) := x0 in (a, x) in f0 a)
        with
          (@fst (A -> B) unit .> flip apply x).
          Focus 2. ext p. destruct p. cbn. reflexivity.
        replace
          (fun x0 : unit * (A -> B) => let '(f0, a) :=
           let '(_, b) := x0 in (fun f0 : A -> B => f0 x, b) in f0 a)
        with
          (@snd unit (A -> B) .> flip apply x).
          Focus 2. ext p. destruct p. cbn. reflexivity.
        rewrite !fmap_pres_comp'. rewrite pairF_default_l, pairF_default_r.
          reflexivity.
    Focus 2. aux.
      replace
      (fun x0 : unit * A =>
       let '(f0, a) := let '(_, b) := x0 in (f, b) in f0 a)
      with
      (@snd unit A .> f).
        Focus 2. ext p. destruct p. cbn. reflexivity.
        rewrite fmap_pres_comp'. rewrite pairF_default_l.
          rewrite <- fmap_pres_comp'. unfold compose. reflexivity.
    aux. aux. repeat aux. *) (*
    replace
    (fun x : ((A -> B) -> A -> C) * (A -> B) * A =>
     let '(f, a) := let '(a, b) := x in (let '(f, a0) := a in f a0, b) in f a)
    with
    (fun x : ((A -> B) -> A -> C) * (A -> B) * A =>
     let '(f, a) := (fst (fst x) (snd (fst x)), snd x) in f a).
    
      Focus 2. ext p. do 2 destruct p. cbn. reflexivity.*)
  Check natural.
    match goal with
        | |- context [pairF (fmap ?f ?a) ?x] =>
            replace x with (fmap id x) by functor;
            rewrite <- ?(natural _ _ _ _ f id a x), <- ?fmap_pres_comp'
    end.
    rewrite fmap_pres_comp.
Abort.

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
    Focus 2. applicative2. unfold compose, par. reflexivity.
    repeat (rewrite <- composition, homomorphism). applicative2.
      unfold compose. reflexivity.
Defined.