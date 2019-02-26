Require Export Control.Applicative.
Require Export Control.Monoidal.

Definition pure_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A : Type} (x : A) : F A :=
    fmap (fun u : unit => x) default.

Definition ap_isMonoidal
  {F : Type -> Type} {inst : isMonoidal F} {A B : Type}
  (f : F (A -> B)) (a : F A) : F B :=
    fmap (fun p => apply (fst p) (snd p)) (pairF f a).

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
Defined.

Definition default_Applicative
  {F : Type -> Type} {inst : Applicative F} : F unit := pure tt.

Definition pairF_Applicative
  {F : Type -> Type} {inst : Applicative F} {A B : Type}
  (x : F A) (y : F B) : F (A * B)%type := pair <$> x <*> y.

Hint Unfold default_Applicative pairF_Applicative : HSLib.

Instance Applicative_isMonoidal
  (F : Type -> Type) (inst : Applicative F) : isMonoidal F :=
{
    isMonoidal_functor := inst;
    default := default_Applicative;
    pairF := @pairF_Applicative F inst;
}.
Proof.
  all: hs;
  repeat (
    rewrite identity || rewrite homomorphism ||
    rewrite fmap_pure_ap || rewrite <- composition ||
    rewrite interchange
  );
  reflexivity.
Defined.