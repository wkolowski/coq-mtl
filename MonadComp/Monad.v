Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export Functor.
Require Export FunctorInst.

Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    ret : forall {A : Type}, A -> M A;
    compM : forall {A B C : Type}, (A -> M B) -> (B -> M C) -> (A -> M C);
    compM_assoc : forall (A B C D : Type) (f : A -> M B) (g : B -> M C)
        (h : C -> M D), compM f (compM g h) = compM (compM f g) h;
    id_left : forall (B C : Type) (g : B -> M C),
        compM ret g = g;
    id_right : forall (A B : Type) (f : A -> M B),
        compM f ret = f
}.

Coercion is_functor : Monad >-> Functor.

Definition bind {A B : Type} {M : Type -> Type} {_ : Monad M}
    (ma : M A) (f : A -> M B) : M B :=
    compM (fun _ : unit => ma) f tt.

Definition join {A : Type} {M : Type -> Type} {_ : Monad M}
    (mma : M (M A)) : M A := bind mma id.

Module MonadNotations.
Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).
End MonadNotations.

Export MonadNotations.

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

Definition bindIgnore {M : Type -> Type} {_ : Monad M} {A B : Type}
    (ma : M A) (mb : M B) : M B := ma >>= fun _ => mb.

Notation "ma >> mb" := (bindIgnore ma mb) (at level 40).

(*Notation "'do' x '<-' e ; e'" := (e >>= fun x => e') (at level 40).
Notation "'do' e1 ; e2" := (e1 >> e2) (at level 40).

Eval compute in do
    x <- [1; 2; 3]; do
    y <- [2; 4; 6];
    ret (x, y).*)

(*Notation "'do' e1 .. eN eN'" :=
    (bindIgnore e1 .. (bindIgnore eN eN') ..) (at level 40).

Eval compute in do
    [1; 2];
    [42; 42];
    [1; 1];
    retM 5.*)

