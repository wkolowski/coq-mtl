Require Export HSLib.Control.Applicative.

(** A [bind]-based definition of monads — the basic one in the library (see
    MonadJoin/Monad.v and Theory/KleisliTriple.v for alternate definitions).
    The intended categorical semantics is a monoidal monad in the category of
    Coq's types and functions.

    The design here is as follows:
    - [Applicative] is a superclass of [Monad]
      (see https://wiki.haskell.org/Functor-Applicative-Monad_Proposal)
    - there is no [return] and [Applicative]'s [pure] is used instead
    - the operators [<<] and [>>] are moved to [Applicative] and replace
      <* and *> respectively.

    There are 4 laws:
    - [bind_pure_l], [bind_pure_r] and [bind_assoc] are standard
    - [bind_ap] ensures that [bind] is compatible with [ap] (and thus
      also with [fmap]) *)
Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_pure_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (pure a) f = f a;
    bind_pure_r :
      forall (A : Type) (ma : M A),
        bind ma pure = ma;
    bind_assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
    bind_ap :
      forall (A B : Type) (mf : M (A -> B)) (mx : M A),
        mf <*> mx = bind mf (fun f => bind mx (fun x => pure (f x)));
}.

Coercion is_applicative : Monad >-> Applicative.

Definition join
  {M : Type -> Type} {inst : Monad M} {A : Type} (mma : M (M A))
    : M A := bind mma id.

Definition compM
  {M : Type -> Type} {inst : Monad M} {A B C : Type}
  (f : A -> M B) (g : B -> M C) (a : A) : M C :=
    bind (f a) g.

(** Basic notations for [bind] and [compM] and a retarded do-notation. The
    retardedness refers to these facts:
    - [e1 >> e2] is written [e1 ;; e2] with double semicolon (instead of
      the single semicolon as in Haskell) because otherwise [Notation] gets
      mad
    - pattern matches (even irrefutable ones) are not allowed
    - you can insert a meanigless 'do' anywhere *)
Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).

Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).

(* TODO
Notation "x '<<--' e1 ;;; e2" := (bind e1 (fun y => let x := y in e2))
  (right associativity, at level 42, only parsing).
*)

Notation "e1 ;; e2" := (constrA e1 e2)
  (right associativity, at level 42, only parsing).

Notation "'do' e" := e (at level 50, only parsing).

End MonadNotations.

Export MonadNotations.

Hint Rewrite @bind_pure_l @bind_pure_r @bind_assoc @bind_ap : HSLib.

(** The main workhorse tactic for most of the library. It proceeds like this:
    - apply the [functional_extensionality] axiom whenever it's possible
    - destruct pairs, sums and [unit]s
    - try to deal with monadic equations containig [>>=] on either side
    - destruct possibly nested pattern matches using tha tactic [unmatch]
      from Base.v
    - if all else fails, use the tactic [hs] from Base.v to automatically
      unfold definitios and perform rewriting
    - after the main loop is done, try [congruence] after some
      simplification *)
Ltac monad := intros; repeat
match goal with
    | |- (fun _ => _) = _ => let x := fresh "x" in ext x
    | |- _ = (fun _ => _) => let x := fresh "x" in ext x
    | x : _ * _ |- _ => destruct x
    | x : _ + _ |- _ => destruct x
    | x : unit |- _ => destruct x
    | |- ?x >>= _ = ?x => rewrite <- bind_pure_r; f_equal
    | |- ?x = ?x >>= _ => rewrite <- bind_pure_r at 1; f_equal
    | |- ?x >>= _ = ?x >>= _ => f_equal; try reflexivity
    | |- context [match ?x with _ => _ end] => hs; unmatch x
    | _ => hs + functor_simpl
end; try (unfold compose, id; cbn; congruence; fail).

(** All functions that in Haskell are doubled between [Applicative] and
    [Monad] in this library are moved to [Applicative] and named with an
    "A" at the end. The versions ending in "M" don't exist, contrary to
    Haskell. *)
Section MonadicFuns.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Fixpoint foldM (f : A -> B -> M A) (dflt : A) (l : list B) : M A :=
match l with
    | [] => pure dflt
    | h :: t => f dflt h >>= fun a : A => foldM f a t
end.

End MonadicFuns.

Arguments foldM {M inst A B} _ _ _.

(** Some of the laws I thought were fundamental, but turned out to be
    redundant. *)
Section DerivedMonadLaws.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Lemma fmap_bind :
  forall (A B C : Type) (x : M A) (f : A -> M B) (g : B -> C),
    fmap g (x >>= f) = x >>= (fun a : A => fmap g (f a)).
Proof.
  intros. hs. f_equal. exts. hs.
Qed.

Lemma bind_fmap :
  forall (A B C : Type) (f : A -> B) (x : M A) (g : B -> M C),
    fmap f x >>= g = x >>= (f .> g).
Proof. monad. Qed.

Lemma fmap_bind_pure :
  forall (A B : Type) (f : A -> B) (x : M A),
    fmap f x = x >>= (fun a : A => pure (f a)).
Proof.
  intros.
  replace (x >>= fun a : A => pure (f a))
  with (pure f >>= fun f => x >>= fun a => pure (f a)).
    rewrite <- bind_ap. rewrite fmap_pure_ap. reflexivity.
    rewrite bind_pure_l. reflexivity.
Qed.

End DerivedMonadLaws.

Hint Rewrite @fmap_bind_pure @bind_fmap @fmap_bind : HSLib.

(** Laws relating fundamental monadic operations ([>>=], [>=>], [join])
    with themselves and other operations, like [fmap] and [>>]. *)
Section DerivedMonadLaws2.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Lemma compM_assoc :
  forall (A B C D : Type) (f : A -> M B) (g : B -> M C) (h : C -> M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
Proof.
  unfold compM. monad.
Qed.

Lemma compM_pure_left :
  forall (A B : Type) (f : A -> M B),
    pure >=> f = f.
Proof.
  unfold compM. monad.
Qed.

Lemma compM_pure_right :
  forall (A B : Type) (f : A -> M B),
    f >=> pure = f.
Proof.
  unfold compM. monad.
Qed.

Lemma compM_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> M C),
    (f .> pure) >=> g = f .> g.
Proof.
  unfold compM, compose. monad.
Qed.

Lemma compM_fmap :
  forall (A B C : Type) (f : A -> M B) (g : B -> C),
    f >=> (g .> pure) = f .> fmap g.
Proof.
  unfold compM, compose. monad.
Qed.

Lemma bind_compM :
  forall (A B : Type) (ma : M A) (f : A -> M B),
    ma >>= f = ((fun _ : unit => ma) >=> f) tt.
Proof.
  unfold compM. monad.
Qed.

Lemma bind_join_fmap :
  forall (A B : Type) (ma : M A) (f : A -> M B),
    ma >>= f = join (fmap f ma).
Proof.
  unfold join. monad.
Qed.

Lemma join_fmap_join :
  forall (A : Type) (x : M (M (M A))),
    join (fmap join x) = join (join x).
Proof.
  unfold join. monad.
Qed.

Lemma join_fmap_pure :
  forall (A : Type) (x : M A),
    join (fmap pure x) = join (pure x).
Proof.
  unfold join. monad.
Qed.

Lemma join_pure :
  forall (A : Type) (x : M A),
    join (pure x) = x.
Proof.
  intros. unfold join. monad.
Qed.

Lemma fmap_join :
  forall (A B C : Type) (f : A -> M B) (g : B -> C) (x : M A),
    fmap g (join (fmap f x)) =
    join (fmap (fun x : A => fmap g (f x)) x).
Proof.
  unfold join. monad.
Qed.

Lemma constrA_assoc :
  forall (A B C : Type) (ma : M A) (mb : M B) (mc : M C),
    (ma >> mb) >> mc = ma >> (mb >> mc).
Proof. unfold constrA, compose. monad. Qed.

Lemma constlA_spec :
  forall (A B : Type) (ma : M A) (mb : M B),
    ma << mb = ma >>= fun a => mb >>= fun _ => pure a.
Proof.
  intros. unfold constlA, compose. monad.
Qed.

Lemma constrA_spec :
  forall (A B : Type) (ma : M A) (mb : M B),
    ma >> mb = ma >>= fun _ => mb.
Proof.
  intros. unfold constrA, compose. monad.
Qed.

End DerivedMonadLaws2.

Hint Rewrite @constlA_spec @constrA_spec : HSLib.