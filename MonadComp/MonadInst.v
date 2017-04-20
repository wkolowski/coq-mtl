Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Functor.Functor.
Require Import HSLib.MonadComp.Monad.

Require Import HSLib.Instances.ListInst.


Fixpoint joinL {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | h :: t => h ++ joinL t
end.

Definition compL {A B C : Type} (f : A -> list B) (g : B -> list C)
    (a : A) : list C := joinL (fmap g (f a)).

Instance MonadList : Monad list :=
{
    is_functor := FunctorList;
    ret := fun (A : Type) (x : A) => [x];
    compM := @compL
}.
Proof.
  intros. extensionality a. unfold compL. induction (f a) as [| h' t'].
    simpl. trivial.
    simpl in *. rewrite IHt'. f_equal. induction (g h').
      simpl. trivial.
      simpl in *. rewrite <- IHl. rewrite app_assoc. trivial.
  intros. extensionality b. unfold compL. simpl. rewrite app_nil_r. trivial.
  intros. extensionality b. unfold compL. induction (f b) as [| h t].
    simpl. trivial.
    simpl. f_equal. assumption.
Defined.

Eval compute in join [[1; 2; 3]; [4; 5; 6]].
Eval compute in [1; 3; 4] >>= fun n : nat => [n; n + 5].
