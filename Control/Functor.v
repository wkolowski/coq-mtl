Require Export HSLib.Base.

(** A standard presentation of Haskell-style functors. The intended
    categorical semantics is a functor in the category of Coq's
    types and functions. Consequences of restricting to only this
    particular category are that all [Functor]s are actually strong
    functors (see below). *)
Class Functor (F : Type -> Type) : Type :=
{
    fmap : forall {A B : Type}, (A -> B) -> (F A -> F B);
    fmap_id :
      forall A : Type, fmap (@id A) = id;
    fmap_comp :
      forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap (f .> g) = fmap f .> fmap g;
}.

Section DerivedFunctorLaws.

Variables
  (F : Type -> Type)
  (inst : Functor F).

(** The basic law [fmap_comp] is problematic for practical use because
    of the right-hand side use of [.>]. A more practically useful law
    is provided here, but the old one is retained for compatibility. *)
Lemma fmap_comp' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : F A),
    fmap (f .> g) x = fmap g (fmap f x).
Proof.
  intros. rewrite fmap_comp. unfold compose. reflexivity.
Qed.

Hint Rewrite @fmap_comp' : HSLib.

(** All [Functor]s are strong. *)
Lemma strength :
  forall A B : Type, A -> F B -> F (A * B)%type.
Proof.
  intros A B a fb. exact (fmap (pair a) fb).
Defined.

End DerivedFunctorLaws.

Hint Rewrite @fmap_id @fmap_comp : HSLib.

(** An implementation of functions that can be found in Haskell's
    Data.Functor. *)
Section FunctorFuns.

Variable F : Type -> Type.
Variable inst : Functor F.
Variables A B : Type.

Definition replaceL (a : A) (fb : F B) : F A :=
  fmap (const a) fb.

Definition replaceR (fa : F A) (b : B) : F B :=
  fmap (const b) fa.

Definition void (ma : F A) : F unit := fmap (fun _ => tt) ma.

End FunctorFuns.

Arguments replaceL {F inst A B} _ _.
Arguments replaceR {F inst A B} _ _.
Arguments void {F inst A} _.

(** Notations mimicking those from Haskell's Data.Functor. The last
    one is used mainly when programming with applicative functors. *)
Infix "<$" := replaceL (at level 40).
Infix "$>" := replaceR (at level 40).
Infix "<$>" := fmap (left associativity, at level 40, only parsing).