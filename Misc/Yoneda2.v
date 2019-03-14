Require Import Functor.
Require Import Control.Monad.Reader.

Variables
  (F : Type -> Type)
  (inst : Functor F)
  (A : Type).

Definition Yoneda : Type :=
  {y : forall B : Type, (A -> B) -> F B |
    forall (B C : Type) (f : A -> B) (g : A -> A),
      fmap f (y A g) = y B (g .> f)}.

Definition abstract (x : F A) : Yoneda.
Proof.
  esplit with (fun (B : Type) (f : A -> B) => fmap f x).
  intros. rewrite <- fmap_comp'. reflexivity.
Defined.

Definition concretize (y : Yoneda) : F A.
Proof.
  destruct y as [y H]. apply y. exact id.
Defined.

Lemma abstract_concretize :
  forall y : Yoneda,
    abstract (concretize y) = y.
Proof.
  destruct y as [y H].
  unfold Yoneda, abstract, concretize. f_equal.
  intros.
Admitted.

Lemma concretize_abstract :
  forall x : F A,
    concretize (abstract x) = x.
Proof.
  unfold Yoneda, abstract, concretize.
  intro. rewrite fmap_id. reflexivity.
Qed.

