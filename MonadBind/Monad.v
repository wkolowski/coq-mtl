Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.Functor.Functor.
Require Export HSLib.Applicative.Applicative.

(* Definition of monad using bind (monadic application). *)
Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_ret_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (ret a) f = f a;
    bind_ret_r :
      forall (A : Type) (ma : M A),
        bind ma ret = ma;
    assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
    bind_fmap :
      forall (A B C : Type) (f : A -> B) (x : M A) (g : B -> M C),
        bind (fmap f x) g = bind x (f .> g);
    fmap_bind :
      forall (A B C : Type) (x : M A) (f : A -> M B) (g : B -> C),
        fmap g (bind x f) = bind x (fun x0 : A => fmap g (f x0));
    bind_ap :
      forall (A B : Type) (mf : M (A -> B)) (mx : M A),
        mf <*> mx = bind mf (fun f => bind mx (fun x => ret (f x)));
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

Section MonadicFuns.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C D E F : Type.

Fixpoint foldM (f : A -> B -> M A) (dflt : A) (l : list B)
    : M A :=
match l with
    | [] => ret dflt
    | h :: t => f dflt h >>= fun a : A => foldM f a t
end.

End MonadicFuns.

Arguments foldM [M] [inst] [A] [B] _ _ _.

Section DerivedLaws.

Variables
  (M : Type -> Type)
  (inst : Monad M).

Theorem compM_assoc :
  forall (A B C D : Type) (f : A -> M B) (g : B -> M C) (h : C -> M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
Proof.
  unfold compM. monad.
Qed.

Theorem compM_id_left :
  forall (A B : Type) (f : A -> M B), ret >=> f = f.
Proof.
  unfold compM. monad.
Qed.

Theorem compM_id_right :
  forall (A B : Type) (f : A -> M B), f >=> ret = f.
Proof.
  unfold compM. monad.
Qed.

Theorem bind_compM :
  forall (A B : Type) (ma : M A) (f : A -> M B),
    bind ma f = ((fun _ : unit => ma) >=> f) tt.
Proof.
  unfold compM. reflexivity.
Qed.

Theorem bind_join_fmap :
  forall (A B C : Type) (ma : M A) (f : A -> M B),
    bind ma f = join (fmap f ma).
Proof.
  unfold join. monad.
Qed.

Theorem join_fmap :
  forall (A : Type) (x : M (M (M A))),
    join (fmap join x) = join (join x).
Proof.
  unfold join. monad.
Qed.

Theorem join_ret :
  forall (A : Type) (x : M A),
    join (ret x) = join (fmap ret x).
Proof.
  unfold join. monad.
Qed.

Theorem fmap_join :
  forall (A B C : Type) (f : A -> M B) (g : B -> C) (x : M A),
    fmap g (join (fmap f x)) =
    join (fmap (fun x : A => fmap g (f x)) x).
Proof.
  intros. unfold join. monad.
Restart.
  unfold join. intros.
  rewrite fmap_bind, 2!bind_fmap. unfold compose, id. reflexivity.
Qed.

End DerivedLaws.