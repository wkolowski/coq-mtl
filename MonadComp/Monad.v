Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.Functor.Functor.
Require Export HSLib.Applicative.Applicative.

(* TODO: Trójka Kleisliego *)

(* Definition of monad using monadic composition. *)
Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
    compM : forall {A B C : Type}, (A -> M B) -> (B -> M C) -> (A -> M C);
    compM_assoc :
      forall (A B C D : Type) (f : A -> M B) (g : B -> M C)
        (h : C -> M D), compM f (compM g h) = compM (compM f g) h;
    compM_ret_l :
      forall (B C : Type) (g : B -> M C),
        compM ret g = g;
    compM_ret_r :
      forall (A B : Type) (f : A -> M B),
        compM f ret = f;
}.

Coercion is_applicative : Monad >-> Applicative.

Definition bind
  {A B : Type} {M : Type -> Type} {_ : Monad M} (ma : M A) (f : A -> M B)
    : M B := compM (fun _ : unit => ma) f tt.

Definition bind_ {M : Type -> Type} {_ : Monad M} {A B : Type}
    (ma : M A) (mb : M B) : M B := bind ma (fun _ => mb).

Definition join {A : Type} {M : Type -> Type} {_ : Monad M}
    (mma : M (M A)) : M A := bind mma id.

Module MonadNotations.

Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "ma >> mb" := (bind_ ma mb) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).

Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).

Notation "e1 ;; e2" := (bind_ e1 e2)
  (right associativity, at level 42, only parsing).

Notation "'do' e" := e (at level 50, only parsing).

End MonadNotations.

Export MonadNotations.

Section MonadicFuns.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Fixpoint foldM {A B : Type} (f : A -> B -> M A) (dflt : A) (l : list B)
    : M A :=
match l with
    | [] => ret dflt
    | h :: t => f dflt h >>= fun a : A => foldM f a t
end.

End MonadicFuns.

Section DerivedLaws.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Print bind.

(* Basic identities for compM version. *)
Theorem compM_join :
  forall (A B C : Type) (f : A -> M B) (g : B -> M C),
    f >=> g = f .> fmap g .> join.
Proof.
  intros. unfold compose. extensionality x.
Abort. (* TODO *)

Theorem compM_bind_eq :
  forall (A B C : Type) (f : A -> M B) (g : B -> M C) (a : A),
    (f >=> g) a = f a >>= g.
Proof.
  intros. unfold bind. destruct inst.
Abort. (* TODO *)

Theorem bind_eq :
  forall (A B : Type) (ma : M A) (f : A -> M B),
    bind ma f = (fmap f .> join) ma.
Proof.
  intros. unfold join, bind, compose.
  cut (((fun _ : unit => ma) >=> f) = ((fun _ : unit => fmap f ma) >=> id)).
    intro. rewrite H. reflexivity.
    unfold id. extensionality x. destruct x.
Abort. (* TODO *)

Theorem ret_bind :
  forall (A B : Type) (x : A) (f : A -> M B),
    ret x >>= f = f x.
Proof.
  intros. unfold bind.
  assert (((fun _ : unit => ret x) >=> f) tt = (ret >=> f) x).
    Focus 2. rewrite H. rewrite compM_ret_l. reflexivity.
    unfold ret, compM. destruct inst, is_applicative.
Admitted. (* TODO *)

Theorem join_law :
  forall A : Type, fmap join .> join = join .> join (A := A).
Proof.
  intros. unfold compose. extensionality x. unfold join.
  unfold id. unfold bind. compute. (*
  f_equal. extensionality y. destruct y. simpl.*)
Abort. (* TODO *)

Theorem ret_law :
  forall A : Type, ret .> join = fmap ret .> join (A := A).
Proof.
  intros. unfold join, compose, id. extensionality x.
  rewrite ret_bind.
Abort. (* TODO *)

End DerivedLaws.