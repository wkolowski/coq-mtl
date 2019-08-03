Require Import Functor.
Require Import Control.Monad.Reader.

Variables
  (F : Type -> Type)
  (inst : Functor F)
  (A : Type).

Definition Yoneda : Type := forall B : Type, (A -> B) -> F B.

Definition abstract (x : F A) : Yoneda :=
  fun (B : Type) (f : A -> B) => fmap f x.

Definition concretize (y : Yoneda) : F A :=
  y A id.

Lemma abstract_concretize :
  forall y : Yoneda,
    abstract (concretize y) = y.
Proof.
  unfold Yoneda, abstract, concretize.
  intros. ext2 B f.
  replace (fmap f (y A id)) with (y B (fmap_Reader f id)).
    reflexivity.
    admit.
Admitted.

Lemma concretize_abstract :
  forall x : F A,
    concretize (abstract x) = x.
Proof.
  unfold Yoneda, abstract, concretize.
  intro. rewrite fmap_id. reflexivity.
Qed.