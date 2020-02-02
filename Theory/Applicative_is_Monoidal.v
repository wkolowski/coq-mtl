(** A proof of the fact the [Applicative] functors are the same thing
    as [Monoidal] functors. *)

Require Export Control.Applicative.
Require Export Control.Monoidal.

(** We cat define [pure] by mapping a constant function over the default
    computation. *)
Definition pure_Monoidal
  {F : Type -> Type} {inst : Monoidal F} {A : Type} (x : A) : F A :=
    fmap (fun u : unit => x) default.

(** We can define [ap] by pairing f with a and mapping over it with a
    function which applies the first component of the pair to the
    second component. *)
Definition ap_Monoidal
  {F : Type -> Type} {inst : Monoidal F} {A B : Type}
  (f : F (A -> B)) (a : F A) : F B :=
    fmap (fun p => apply (fst p) (snd p)) (pairF f a).

(** The direction [Monoidal] => [Applicative] was very hard for me to
    prove. After unfolding definitions, the easy part is taken care of
    by the tactic [monoidal]. The rest is mostly precisely tailored
    rewrites in the reverse direction. If you gazed at the goals for
    long enough, you could probably have proved this all by yourself,
    but thanks to me you don't need to... *)
#[refine]
Instance Monoidal_Applicative
  (F : Type -> Type) (inst : Monoidal F) : Applicative F :=
{
    is_functor := @is_functor F inst;
    pure := @pure_Monoidal F inst;
    ap := @ap_Monoidal F inst
}.
Proof.
  all: unfold pure_Monoidal, ap_Monoidal; intros; monoidal.
    rewrite !par_comp. cbn. unfold apply.
      rewrite <- (pairF_default_l _ (pairF g (pairF f x))).
      rewrite <- ?pairF_assoc, <- ?fmap_comp'. repeat f_equal.
      ext p. destruct p as [[[u g'] f'] x']. cbn. reflexivity.
    rewrite <- fmap_comp'. reflexivity.
    rewrite <- fmap_comp', par_comp. cbn.
      replace (fun p : (A -> B) * unit => id (fst p) x)
      with (@fst (A -> B) unit .> flip apply x).
        monoidal. unfold flip, apply, id, compose. reflexivity.
        ext p. destruct p. cbn. reflexivity.
Defined.

(** We can define [default] by injecting [tt] into the functor. *)
Definition default_Applicative
  {F : Type -> Type} {inst : Applicative F} : F unit := pure tt.

(** We can define [pairF] by applying [pair] injected into the functor. *)
Definition pairF_Applicative
  {F : Type -> Type} {inst : Applicative F} {A B : Type}
  (x : F A) (y : F B) : F (A * B)%type := pair <$> x <*> y.

Hint Unfold default_Applicative pairF_Applicative : CoqMTL.

(*Hint Remove fmap_pure_ap : CoqMTL.*)

(** The proof is quite easy, nothing to see here.
    Note that [fmap_pure_ap] is not necessary in the big rewrite
    alternative ||, but the tactic [hs] uses it, so it's necessary
    to prove the equivalence. *)
#[refine]
Instance Applicative_Monoidal
  (F : Type -> Type) (inst : Applicative F) : Monoidal F :=
{
    is_functor := inst;
    default := default_Applicative;
    pairF := @pairF_Applicative F inst;
}.
Proof.
  all: hs;
  repeat (
    rewrite identity || rewrite homomorphism ||
    (*rewrite fmap_pure_ap ||*) rewrite <- composition ||
    rewrite interchange
  );
  reflexivity.
Defined.