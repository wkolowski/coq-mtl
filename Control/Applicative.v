From CoqMTL Require Export Control.Functor.

(** Haskell-style applicative functors. The intended categorical semantics
    is a (strong) monoidal functor in the category of Coq's types and
    functions (see Control.Monoidal for more).

    Currently there are 5 laws, four of which ([identity], [composition],
    [homomorphism] and [interchange]) are standard and the fifth one,
    [fmap_pure_ap], ensures compatibility with the given [Functor] instance.
    These laws are redundant: [identity] follows from [fmap_pure_ap]. *)
Class Applicative (F : Type -> Type) : Type :=
{
  is_functor :> Functor F;
  pure : forall {A : Type}, A -> F A;
  ap : forall {A B : Type}, F (A -> B) -> F A -> F B;
  identity :
    forall (A : Type) (ax : F A), ap (pure id) ax = ax;
  composition :
    forall
      (A B C : Type)
      (f : F (A -> B)) (g : F (B  -> C)) (x : F A),
        ap (ap (ap (pure compose) g) f) x = ap g (ap f x);
  homomorphism :
    forall (A B : Type) (f : A -> B) (x : A),
      ap (pure f) (pure x) = pure (f x);
  interchange :
    forall (A B : Type) (f : F (A -> B)) (x : A),
      ap f (pure x) = ap (pure (fun f => f x)) f;
  fmap_pure_ap :
    forall (A B : Type) (f : A -> B) (x : F A),
      fmap f x = ap (pure f) x;
}.

Coercion is_functor : Applicative >-> Functor.

#[global] Hint Rewrite @composition @homomorphism @fmap_pure_ap : CoqMTL.
#[global] Hint Rewrite <- @interchange : CoqMTL.

Module ApplicativeNotations.

(** A custom notation that is meant to replace both ordinary function
    application (denoted $ in Haskell) and applicative functor's [ap]
    (denoted <*> in Haskell and here too — see below). Note that these
    two coincide for the [Applicative] instance of the [Identity] functor.
    However, it is not currently used and awaits a better future. *)
Notation "f $$ x" := (ap f x)
  (left associativity, at level 40, only parsing).

Notation "f <*> x" := (ap f x)
  (left associativity, at level 40).

Notation "x <**> f" := (ap f x)
  (left associativity, at level 40, only parsing).

Definition constlA
  {F : Type -> Type} {inst : Applicative F} {A B : Type} (a : F A) (b : F B)
    : F A := const <$> a <*> b.

Definition constrA
  {F : Type -> Type} {inst : Applicative F} {A B : Type} (a : F A) (b : F B)
    : F B := (const .> fmap) id a <*> b.

(** In Haskell [constlA] and [constrA] are called <* and *> respectively and
    << and >> are their monadic counterparts. Here we get rid of the doubled
    [Applicative]/[Monad] versions and of the ugly *> and <* notations and
    use << and >> in all contexts. This has some technical consequences
    (we will need a few lemmas for dealing with [>>] in monadic contexts. *)
Infix "<<" := constlA (right associativity, at level 42).
Infix ">>" := constrA (right associativity, at level 42).

End ApplicativeNotations.

Export ApplicativeNotations.

Section DerivedApplicativeLaws.

Variables
  (F : Type -> Type)
  (inst : Applicative F).

Lemma fmap_pure :
  forall (A B : Type) (f : A -> B) (x : A),
    fmap f (pure x) = pure (f x).
Proof. hs. Qed.

Lemma constrA_pure_l :
  forall (A B : Type) (a : A) (fb : F B),
    pure a >> fb = fb.
Proof.
  intros. unfold constrA, compose.
  rewrite fmap_pure_ap, homomorphism, identity.
  reflexivity.
Qed.

Hint Rewrite @fmap_pure constrA_pure_l : CoqMTL.

End DerivedApplicativeLaws.

(** Utility functions for applicative functors. In Haskell, most of these
    require the [F] to be a monad, but in this library they require only
    an [Applicative]. They are consistently named with "A" at the end and
    the ones with "M" at the end you can find in Haskell don't exist here. *)
Section ApplicativeFuns1.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D E : Type.

Definition liftA2
  (f : A -> B -> C)
  (fa : F A) (fb : F B) : F C :=
    pure f <*> fa <*> fb.

Definition liftA3
  (f : A -> B -> C -> D)
  (fa : F A) (fb : F B) (fc : F C) : F D :=
    pure f <*> fa <*> fb <*> fc.

Definition liftA4
  (f : A -> B -> C -> D -> E)
  (fa : F A) (fb : F B) (fc : F C) (fd : F D) : F E :=
    pure f <*> fa <*> fb <*> fc <*> fd.

Fixpoint filterA (p : A -> F bool) (la : list A) : F (list A) :=
match la with
| [] => pure []
| h :: t =>
    let f :=
      fmap (fun b : bool => if b then (cons h) else id) (p h)
    in f <*> filterA p t
end.

Fixpoint sequenceA (lma : list (F A)) : F (list A) :=
match lma with
| [] => pure []
| h :: t => cons <$> h <*> sequenceA t
end.

Fixpoint replicateA (n : nat) (x : F A) : F (list A) :=
match n with
| 0 => pure []
| S n' => cons <$> x <*> replicateA n' x
end.

Fixpoint zipWithA (f : A -> B -> F C) (la : list A) (lb : list B)
    : F (list C) :=
match la, lb with
| [], _ => pure []
| _, [] => pure []
| ha :: ta, hb :: tb =>
    cons <$> f ha hb <*> zipWithA f ta tb
end.

Definition when (cond : bool) (a : F unit) : F unit :=
  if cond then a else pure tt.

Definition unless (cond : bool) (a : F unit) : F unit :=
  if cond then pure tt else a.

End ApplicativeFuns1.

Arguments liftA2 {F inst A B C} _ _ _.
Arguments liftA3 {F inst A B C D} _ _ _ _.
Arguments liftA4 {F inst A B C D E} _ _ _ _ _.

Arguments filterA {F inst A} _ _.
Arguments sequenceA {F inst A} _.
Arguments replicateA {F inst A} _ _.
Arguments zipWithA {F inst A B C} _ _ _.
Arguments when {F inst} _ _.
Arguments unless {F inst} _ _.

Section ApplicativeFuns2.

Variable F : Type -> Type.
Variable inst : Applicative F.
Variables A B C D E : Type.

Definition mapA (f : A -> F B) (la : list A) : F (list B) :=
  sequenceA (map f la).

Definition forA (la : list A) (f : A -> F B) : F (list B) :=
  mapA f la.

End ApplicativeFuns2.