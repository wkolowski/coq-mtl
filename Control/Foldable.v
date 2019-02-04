Require Export HSLib.Base.
Require Export HSLib.Misc.Monoid.

(** Haskell-style [Foldable]. I have no idea about the intended categorical
    semantics. The definition is based on [foldMap] while [foldr] and [foldl]
    are moved outside and are implemented in terms of [foldMap].

    There's one law I haven't thought much about and it's stated uglily
    (a definition of monoid homomorphisms would help a lot). *)
Class Foldable (T : Type -> Type) : Type :=
{
    foldMap : forall {A : Type} {M : Monoid}, (A -> M) -> T A -> M;
    foldMap_law :
      forall (A : Type) (B C : Monoid) (f : A -> B) (g : B -> C),
        g neutr = neutr -> (forall x y : B, g (op x y) = op (g x) (g y)) ->
          foldMap (f .> g) = foldMap f .> g
}.

(** A monoid instance for functions with composition and identity. It is
    needed to define [foldr] and [foldl] using [foldMap]. *)
Instance Endo (A : Type) : Monoid :=
{
    carr := A -> A;
    op := @compose A A A;
    neutr := id;
}.
Proof. all: hs. Defined.

(** Utility functions taken from Haskell's Data.Foldable. *)
Section FoldableFuns.

Variable A B C : Type.
Variable T : Type -> Type.
Variable inst : Foldable T.
Variable M : Monoid.

(** Note that [foldr'], [foldl'] are not present because laziness is not a
    problem while [foldr1] and [foldl1] are not present because the case
    of an empty structure just cannot be omitted. *)
Definition foldr
  {A B : Type} (f : A -> B -> B) (dflt : B) (t : T A) : B :=
    @foldMap T inst A (Endo B) (fun a : A => f a) t dflt.

Definition foldl
  {A B : Type} (f : B -> A -> B) (dflt : B) (t : T A) : B :=
    @foldMap T inst A (Endo B) (fun a : A => flip f a) t dflt.

Definition fold (t : T M) : M := foldr op neutr t.

Definition isEmpty (ta : T A) : bool :=
  foldr (fun _ _ => false) true ta.

Definition size (ta : T A) : nat :=
  foldr (fun _ n => S n) 0 ta.

Definition toListF (ta : T A) : list A :=
  foldr (fun h t => h :: t) [] ta.

Definition elem (cmp : A -> A -> bool) (a : A) (ta : T A) : bool :=
  foldr (fun x y => if cmp a x then true else y) false ta.

Require Import Arith.

Definition maxF (tn : T nat) : nat :=
  foldr (fun n m => if leb n m then m else n) 0 tn.

Definition maxBy (cmp : A -> A -> bool) (dflt : A) (ta : T A) : A :=
  foldr (fun x xs => if cmp x xs then xs else x) dflt ta.

Definition minBy (cmp : A -> A -> bool) (dflt : A) (ta : T A) : A :=
  maxBy (fun a a' => negb (cmp a a')) dflt ta.

Definition andF (tb : T bool) : bool :=
  foldr (fun p q => andb p q) true tb.

Definition orF (tb : T bool) : bool :=
  foldr (fun p q => orb p q) false tb.

Definition allF (f : A -> bool) (ta : T A) : bool :=
  foldr (fun x xs => andb (f x) xs) true ta.

Definition anyF (f : A -> bool) (ta : T A) : bool :=
  foldr (fun x xs => orb (f x) xs) false ta.

Definition findFirst (f : A -> bool) (ta : T A) : option A :=
  foldr (fun x xs => if f x then Some x else xs) None ta.

Definition count (f : A -> bool) (ta : T A) : nat :=
  foldr (fun x n => if f x then S n else n) 0 ta.

Definition findAll (f : A -> bool) (ta : T A) : list A :=
  foldr (fun x xs => if f x then x :: xs else xs) [] ta.

End FoldableFuns.

Arguments foldr {T inst A B} _ _ _.
Arguments foldl {T inst A B} _ _ _.
Arguments isEmpty {A T inst} _.
Arguments size {A T inst} _.
Arguments toListF {A T inst} _.
Arguments elem {A T inst} _ _ _.
Arguments maxF {T inst} _.
Arguments maxBy {A T inst} _ _ _.
Arguments minBy {A T inst} _ _ _.
Arguments maxBy {A T inst} _ _ _.
Arguments findFirst {A T inst} _ _.
Arguments count {A T inst} _ _.
Arguments findAll {A T inst} _ _.
Arguments andF {T inst} _.
Arguments orF {T inst} _.
Arguments allF {A T inst} _ _.
Arguments anyF {A T inst} _ _.

(** Some laws. *)

Lemma isEmpty_size :
  forall (F : Type -> Type) (inst : Foldable F) (A : Type) (x : F A),
    isEmpty x = true <-> size x = 0.
Proof.
  split.
    unfold isEmpty, size, foldr. intro.
    Focus 2. unfold size, isEmpty, foldr.
Admitted.