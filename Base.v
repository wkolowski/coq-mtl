(** This file is at the root of the whole library. All other files depend
    on it. *)

Require Export List.
Export ListNotations.

(** All definitions are universe polymorphic. Things are not that fine
    however: I encountered universe inconsistencies a few times. *)
Global Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** Useful shorthand tactics for doing generalization and inversion. *)
Ltac gen x := generalize dependent x.
Ltac inv H := inversion H; subst; clear H.

(** We will reason by functional extensionality quite a lot. For this, we
    have three tactics:
    - [ext x] is a shorthand for [extensionality x]
    - [ext] is [ext x], where x is a freshly generated name
    - [exts] is repeated [ext] *)
Require Export Coq.Logic.FunctionalExtensionality.

Ltac ext_aux x := extensionality x.

Tactic Notation "ext" ident(x) := extensionality x.
Tactic Notation "ext2" ident(x) ident(y) := ext x; ext y.
Tactic Notation "ext3" ident(x) ident(y) ident(z) := ext x; ext y; ext z.
Tactic Notation "ext4" ident(x) ident(y) ident(z) ident(w) :=
  ext x; ext y; ext z; ext w.

Tactic Notation "ext" := let x := fresh "x" in ext x.
Ltac exts := repeat ext.

(** Program.Basics has the rest of the things we need, namely [id] and
    [compose]. For composition, there's a forward-style notation f .> g
    and for function application without too many parentheses there's
    Haskell's $. *)
Require Export Coq.Program.Basics.

Notation "f .> g" := (compose g f) (at level 40).
Notation "f $ x" := (f x) (right associativity, at level 30, only parsing).

(** We will need some obvious lemmas about [id]. *)
Lemma id_eq :
  forall (A : Type) (x : A), id x = x.
Proof. reflexivity. Qed.

Lemma id_left :
  forall (A B : Type) (f : A -> B),
    id .> f = f.
Proof.
  intros. unfold compose, id. ext x. reflexivity.
Qed.

Lemma id_right :
  forall (A B : Type) (f : A -> B),
    f .> id = f.
Proof.
  intros. unfold compose, id. ext x. reflexivity.
Qed.

(** Our main tactics, [hs] and [monad] are based on [autorewrite] and
    [autounfold]. These two repeatedly rewrite/unfold all things they
    find in their hint databases. Throughout the library, we will need
    to mark which lemmas and definitions we want rewritten/unfolded.

    We need to make sure the rewriting doesn't loop and that unfolding
    doesn't prevent rewriting. In practice, this is very straightforward.
    We will only add as hints those lemmas that "simplify", in some
    subjective sense, the theorem's statement. Since rewriting is
    performed before unfolding, we don't need to worry about it breaking
    anything.

    Both our rewriting and unfolding main hint databses are named
    [HSLib], but there are some minor ones, like [HSLib'], [Functor]
    and [Functor']. *)
Hint Rewrite @id_eq @id_left @id_right : HSLib HSLib'.

(** Note that rewriting and unfolding databases are separate, so we have
    to define a dummy value and add it to the unfolding database in order
    to initialize it. *)
Definition the_ultimate_answer := 42.

Hint Unfold the_ultimate_answer : HSLib HSLib'.

(** [msimpl] is the main simplification tactic we will use. We first rewrite
    and then unfold using the rewrite/hint databases both named [HSLib].

    [msimpl'] is a variant that tries to perform some simplications from
    the hint database [HSLib'] that could result in nontermination if they
    were added to [HSLib]. *)
Ltac msimpl :=
  repeat (autorewrite with HSLib + autounfold with HSLib).

Ltac msimpl' :=
  repeat (autorewrite with HSLib' + autounfold with HSLib).

(** [hs] is a tactic for dealing with simple goals. First we try
    [reflexivity] to make proofterms short, then we simplify and
    at last we try [congruence] to solve trivial equational goals.

    [hs'] is a variant that uses the [msimpl'] simplification tactic
    instead of [msimpl]. *)
Ltac hs :=
  cbn; intros; msimpl; try congruence; try reflexivity.

Ltac hs' :=
  cbn; intros; msimpl'; try congruence; try reflexivity.

(** [umatch] and [unmatch_all] are tactics for conveniently [destruct]ing
    nested pattern matches. *)
Ltac unmatch x :=
match x with
    | context [match ?y with _ => _ end] => unmatch y
    | _ => destruct x
end.

Ltac unmatch_all :=
match goal with
    | |- context [match ?x with _ => _ end] => unmatch x
end.

(** A nice name for the identity function stolen from Idris. Probably not
    very useful. *)
Definition the (A : Type) (x : A) : A := x.