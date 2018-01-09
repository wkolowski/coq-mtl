Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.Base.
Require Import HSLib.Instances.ListInst.

Require Export HSLib.Functor.Functor.
Require Export HSLib.Applicative.Applicative.

(* Definition of monad using ret and bind. *)
Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_ret_l : forall (A B : Type) (f : A -> M B) (a : A),
      bind (ret a) f = f a;
    bind_ret_r : forall (A : Type) (ma : M A),
      bind ma ret = ma;
    assoc : forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
      bind (bind ma f) g = bind ma (fun x => bind (f x) g);
    bind_fmap : forall (A B C : Type) (f : A -> B) (x : M A) (g : B -> M C),
      bind (fmap f x) g = bind x (f .> g);
    fmap_bind :
      forall (A B C : Type) (x : M A) (f : A -> M B) (g : B -> C),
        fmap g (bind x f) = bind x (fun x0 : A => fmap g (f x0));
    bind_ap :
      forall (A B : Type) (mf : M (A -> B)) (mx : M A),
        ap mf mx = bind mf (fun f => bind mx (fun x => ret (f x)));
}.

Coercion is_applicative : Monad >-> Applicative.

Definition bind_
  {M : Type -> Type} {_ : Monad M} {A B : Type} (ma : M A) (mb : M B)
    : M B := bind ma (fun _ => mb).

Definition join
  {M : Type -> Type} {_inst : Monad M} {A : Type} (mma : M (M A))
    : M A := bind mma id.

Definition compM
  {M : Type -> Type} {_inst : Monad M} {A B C : Type}
  (f : A -> M B) (g : B -> M C) (a : A) : M C :=
    bind (f a) g.

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

Hint Rewrite @bind_ret_l @bind_ret_r @assoc @bind_fmap @fmap_bind @bind_ap
  : monad_laws.

Ltac monad' :=
  intros;
  autorewrite with monad_laws;
  autorewrite with applicative_laws.

Ltac monad :=
repeat (monad'; repeat match goal with
    | H : _ * _ |- _ => destruct H
    | |- ?x >>= _ = ?x => rewrite <- bind_ret_r
    | |- ?x >>= _ = ?x >>= _ => f_equal
    | |- (fun _ => _) = _ => let x := fresh "x" in ext x
    | |- _ = (fun _ => _) => let x := fresh "x" in ext x
    | |- context [match ?x with _ => _ end] => destruct x
end; monad'); try (unfold compose, id; cbn; congruence; fail).

(*Section Lifts.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

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

Arguments liftM2 [M inst A B C] _ _ _.
Arguments liftM3 [M inst A B C D] _ _ _ _.
Arguments liftM4 [M inst A B C D E] _ _ _ _ _.
Arguments liftM5 [M inst A B C D E F] _ _ _ _ _ _.*)

Section MonadicFuns.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

(*Fixpoint filterM (f : A -> M bool) (la : list A) : M (list A) :=
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
end.*)

Fixpoint foldM (f : A -> B -> M A) (dflt : A) (l : list B)
    : M A :=
match l with
    | [] => ret dflt
    | h :: t => f dflt h >>= fun a : A => foldM f a t
end.

(*Definition when (b : bool) (mu : M unit) : M unit :=
match b with
    | true => mu
    | false => ret tt
end.

Definition unless (b : bool) (mu : M unit) : M unit :=
    when (negb b) mu.*)

End MonadicFuns.

(*Arguments filterM [M] [inst] [A] _ _.
Arguments sequence [M] [inst] [A] _.
Arguments replicateM [M] [inst] [A] _ _.
Arguments zipWithM [M] [inst] [A] [B] [C] _ _ _.*)
Arguments foldM [M] [inst] [A] [B] _ _ _.
(*Arguments when [M] [inst] _ _.
Arguments unless [M] [inst] _ _.*)

(*Section MonadicFuns2.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Definition mapM (f : A -> M B) (la : list A) : M (list B) :=
  sequence (fmap f la).

Definition forM (la : list A) (f : A -> M B) : M (list B) :=
  mapM f la.

End MonadicFuns2.

Arguments mapM [M] [inst] [A] [B] _ _.
Arguments forM [M] [inst] [A] [B] _ _.*)

Section DerivedLaws.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Theorem compM_assoc :
  forall (A B C D : Type) (f : A -> M B) (g : B -> M C) (h : C -> M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
Proof.
  intros. unfold compM. ext a. rewrite assoc. reflexivity.
Qed.

Theorem compM_id_left :
  forall (A B : Type) (f : A -> M B), ret >=> f = f.
Proof.
  intros. unfold compM. ext a. apply bind_ret_l.
Qed.

Theorem compM_id_right :
  forall (A B : Type) (f : A -> M B), f >=> ret = f.
Proof.
  intros. unfold compM. ext a. apply bind_ret_r.
Qed.

Theorem bind_compM :
  forall (A B : Type) (ma : M A) (f : A -> M B),
    bind ma f = ((fun _ : unit => ma) >=> f) tt.
Proof.
  intros. unfold compM. reflexivity.
Qed.

Theorem bind_join_fmap :
  forall (A B C : Type) (ma : M A) (f : A -> M B),
    bind ma f = join (fmap f ma).
Proof.
  intros. unfold join. rewrite bind_fmap. reflexivity.
Qed.

Theorem join_fmap :
  forall (A : Type) (x : M (M (M A))),
    join (fmap join x) = join (join x).
Proof.
  intros. unfold join. rewrite bind_fmap, assoc. reflexivity.
Qed.

Theorem join_ret :
  forall (A : Type) (x : M A),
    join (ret x) = join (fmap ret x).
Proof.
  intros. unfold join.
  rewrite bind_ret_l, bind_fmap, id_right, bind_ret_r.
  reflexivity.
Qed.

End DerivedLaws.