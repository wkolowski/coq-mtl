Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Instances.ListInst.

Require Import HSLib.Functor.Functor.
Require Import HSLib.Functor.FunctorInst.

(* Definition of monad using ret and monadic composition. *)
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

Definition bind_ {M : Type -> Type} {_ : Monad M} {A B : Type}
    (ma : M A) (mb : M B) : M B := bind ma (fun _ => mb).

Definition join {A : Type} {M : Type -> Type} {_ : Monad M}
    (mma : M (M A)) : M A := bind mma id.

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

Fixpoint sequence {M : Type -> Type} {_xd : Monad M} {A : Type}
    (lma : list (M A)) : M (list A) :=
match lma with
    | [] => ret []
    | h :: t => liftM2 (@cons A) h (sequence t)
end.

Fixpoint replicateM {A : Type} (n : nat) (ma : M A) : M (list A) :=
match n with
    | 0 => ret []
    | S n' => liftM2 (@cons A) ma (replicateM n' ma)
end.

Definition mapM {A B : Type} (f : A -> M B) : list A -> M (list B) :=
    fmap f .> sequence.

Definition forM {A B : Type} (la : list A) (f : A -> M B) : M (list B) :=
    mapM f la.

Fixpoint zipWithM {A B C : Type} (f : A -> B -> M C)
    (la : list A) (lb : list B) : M (list C) :=
match la, lb with
    | [], _ => ret []
    | _, [] => ret []
    | ha :: ta, hb :: tb => liftM2 (@cons C) (f ha hb) (zipWithM f ta tb)
end.

Fixpoint foldM {A B : Type} (f : A -> B -> M A) (dflt : A) (l : list B)
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