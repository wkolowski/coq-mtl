Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Instances.ListInst.

Require Import HSLib.Functor.Functor.

(* Definition of monad using ret and bind. *)
Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    ret : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    id_left : forall (A B : Type) (f : A -> M B) (a : A),
        bind (ret a) f = f a;
    id_right : forall (A : Type) (ma : M A),
        bind ma ret = ma;
    assoc : forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g)
}.

Coercion is_functor : Monad >-> Functor.

Definition bind_ {M : Type -> Type} {_ : Monad M} {A B : Type}
    (ma : M A) (mb : M B) : M B := bind ma (fun _ => mb).

Definition join {M : Type -> Type} {_inst : Monad M} {A : Type}
    (mma : M (M A)) : M A := bind mma id.

Definition compM {M : Type -> Type} {_inst : Monad M} {A B C : Type}
    (f : A -> M B) (g : B -> M C) (a : A) : M C :=
    bind (f a) g.

Module MonadNotations.
Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "ma >> mb" := (bind_ ma mb) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).
End MonadNotations.

Export MonadNotations.

Section Lifts.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Definition liftM
    (f : A -> B)
    (ma : M A) : M B :=
    ma >>= fun a : A => ret (f a).

Definition liftM2
    (f : A -> B -> C)
    (ma : M A) (mb : M B) : M C :=
    ma >>= fun a : A =>
    mb >>= fun b : B => ret (f a b).

Definition liftM3
    (f : A -> B -> C -> D)
    (ma : M A) (mb : M B) (mc : M C) : M D :=
    ma >>= fun a : A =>
    mb >>= fun b : B => 
    mc >>= fun c : C => ret (f a b c).

Definition liftM4
    (f : A -> B -> C -> D -> E)
    (ma : M A) (mb : M B) (mc : M C) (md : M D) : M E :=
    ma >>= fun a : A =>
    mb >>= fun b : B =>
    mc >>= fun c : C =>
    md >>= fun d : D => ret (f a b c d).

Definition liftM5
    (f : A -> B -> C -> D -> E -> F)
    (ma : M A) (mb : M B) (mc : M C) (md : M D) (me : M E) : M F :=
    ma >>= fun a : A =>
    mb >>= fun b : B =>
    mc >>= fun c : C =>
    md >>= fun d : D =>
    me >>= fun e : E => ret (f a b c d e).

End Lifts.

Arguments liftM [M] [inst] [A] [B] _ _.
Arguments liftM2 [M] [inst] [A] [B] [C] _ _ _.
Arguments liftM3 [M] [inst] [A] [B] [C] [D] _ _ _ _.
Arguments liftM4 [M] [inst] [A] [B] [C] [D] [E] _ _ _ _ _.
Arguments liftM5 [M] [inst] [A] [B] [C] [D] [E] [F] _ _ _ _ _ _.

Section MonadicFuns.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

(* TODO remove after Applicative is superclass of Monad. *)
Definition ap (mf : M (A -> B)) (ma : M A) : M B :=
    mf >>= fun f =>
    ma >>= fun a => ret (f a).

Fixpoint filterM (f : A -> M bool) (la : list A) : M (list A) :=
match la with
    | [] => ret []
    | h :: t => f h >>= fun b : bool => if b
        then liftM2 (@cons A) (ret h) (filterM f t)
        else filterM f t
end.

Fixpoint sequence
    (lma : list (M A)) : M (list A) :=
match lma with
    | [] => ret []
    | h :: t => liftM2 (@cons A) h (sequence t)
end.

Fixpoint replicateM (n : nat) (ma : M A) : M (list A) :=
match n with
    | 0 => ret []
    | S n' => liftM2 (@cons A) ma (replicateM n' ma)
end.

Fixpoint zipWithM (f : A -> B -> M C)
    (la : list A) (lb : list B) : M (list C) :=
match la, lb with
    | [], _ => ret []
    | _, [] => ret []
    | ha :: ta, hb :: tb => liftM2 (@cons C) (f ha hb) (zipWithM f ta tb)
end.

Fixpoint foldM (f : A -> B -> M A) (dflt : A) (l : list B)
    : M A :=
match l with
    | [] => ret dflt
    | h :: t => f dflt h >>= fun a : A => foldM f a t
end.

Definition when (b : bool) (mu : M unit) : M unit :=
match b with
    | true => mu
    | false => ret tt
end.

Definition unless (b : bool) (mu : M unit) : M unit :=
    when (negb b) mu.

End MonadicFuns.

Arguments ap [M] [inst] [A] [B] _ _.
Arguments filterM [M] [inst] [A] _ _.
Arguments sequence [M] [inst] [A] _.
Arguments replicateM [M] [inst] [A] _ _.
Arguments zipWithM [M] [inst] [A] [B] [C] _ _ _.
Arguments foldM [M] [inst] [A] [B] _ _ _.
Arguments when [M] [inst] _ _.
Arguments unless [M] [inst] _ _.

Section MonadicFuns2.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Definition mapM (f : A -> M B) (la : list A) : M (list B) :=
    sequence (fmap f la).

Definition forM (la : list A) (f : A -> M B) : M (list B) :=
    mapM f la.

End MonadicFuns2.

Arguments mapM [M] [inst] [A] [B] _ _.
Arguments forM [M] [inst] [A] [B] _ _.

Theorem compM_assoc :
  forall (M : Type -> Type) (inst : Monad M) (A B C D : Type)
  (f : A -> M B) (g : B -> M C) (h : C -> M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
Proof.
  intros. unfold compM. extensionality a.
  rewrite assoc. f_equal.
Qed.

Theorem compM_id_left :
  forall (M : Type -> Type) (inst : Monad M)
  (B C : Type) (g : B -> M C),
    ret >=> g = g.
Proof.
  intros. unfold compM. extensionality b.
  rewrite !id_left. reflexivity.
Qed.

Theorem compM_id_right :
  forall (M : Type -> Type) (inst : Monad M)
  (A B : Type) (f : A -> M B),
    f >=> ret = f.
Proof.
  intros. unfold compM. extensionality a.
  rewrite id_right. reflexivity.
Qed.

Theorem bind_compM_eq :
  forall (M : Type -> Type) (inst : Monad M) (A B : Type)
  (ma : M A) (f : A -> M B),
    bind ma f = ((fun _ : unit => ma) >=> f) tt.
Proof.
  intros. unfold compM. reflexivity.
Qed.

Theorem bind_eq_join :
  forall (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (ma : M A) (f : A -> M B),
    bind ma f = (fmap f .> join) ma.
Proof.
  intros. unfold join, compose. unfold id.

Theorem join_law :
  forall (M : Type -> Type) (inst : Monad M) (X : Type),
    fmap join .> join = join .> @join M inst X.
Proof.
  intros. unfold compose. extensionality x. unfold join.
  Print Functor.
  unfold id. Print Monad. rewrite assoc. simpl.
Abort.
Theorem ret_law :
  forall (M : Type -> Type) (inst : Monad M) (X : Type),
    ret .> join = fmap ret .> @join M inst X.
Proof.
  intros. unfold join, compose, id. extensionality x.
  rewrite id_left. Print Monad. 