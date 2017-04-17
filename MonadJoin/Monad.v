Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export HSLib.Functor.Functor.
Require Export HSLib.Functor.FunctorInst.

(* Definition of monad using ret and join. *)
Class Monad (M : Type -> Type) : Type :=
{
    is_functor :> Functor M;
    ret : forall {A : Type}, A -> M A;
    join : forall {A : Type}, M (M A) -> M A;
    join_law : forall (X : Type),
        fmap join .> join = join .> @join X;
    ret_law : forall (X : Type),
        ret .> join = fmap ret .> @join X
}.

Coercion is_functor : Monad >-> Functor.

Definition bind {A B : Type} {M : Type -> Type} {_ : Monad M}
    (ma : M A) (f : A -> M B) : M B :=
    (fmap f .> join) ma.

Definition compM {A B C : Type} {M : Type -> Type} {_ : Monad M}
    (f : A -> M B) (g : B -> M C) : A -> M C :=
    f .> fmap g .> join.

Module MonadNotations.
Notation "mx >>= f" := (bind mx f) (at level 40).
Notation "f >=> g" := (compM f g) (at level 40).
End MonadNotations.

Export MonadNotations.

(* lifts *)
Definition liftM {M : Type -> Type} {_ : Monad M} {A B : Type}
    (f : A -> B)
    (ma : M A) : M B :=
    ma >>= fun a : A => ret (f a).

Definition liftM2 {M : Type -> Type} {_ : Monad M} {A B C : Type}
    (f : A -> B -> C)
    (ma : M A) (mb : M B) : M C :=
    ma >>= fun a : A =>
    mb >>= fun b : B => ret (f a b).

Definition liftM3 {M : Type -> Type} {_ : Monad M} {A B C D : Type}
    (f : A -> B -> C -> D)
    (ma : M A) (mb : M B) (mc : M C) : M D :=
    ma >>= fun a : A =>
    mb >>= fun b : B => 
    mc >>= fun c : C => ret (f a b c).

Definition liftM4 {M : Type -> Type} {_ : Monad M} {A B C D E : Type}
    (f : A -> B -> C -> D -> E)
    (ma : M A) (mb : M B) (mc : M C) (md : M D) : M E :=
    ma >>= fun a : A =>
    mb >>= fun b : B =>
    mc >>= fun c : C =>
    md >>= fun d : D => ret (f a b c d).

Definition liftM5 {M : Type -> Type} {_ : Monad M} {A B C D E F : Type}
    (f : A -> B -> C -> D -> E -> F)
    (ma : M A) (mb : M B) (mc : M C) (md : M D) (me : M E) : M F :=
    ma >>= fun a : A =>
    mb >>= fun b : B =>
    mc >>= fun c : C =>
    md >>= fun d : D =>
    me >>= fun e : E => ret (f a b c d e).

Definition ap {M : Type -> Type} {_ : Monad M} {A B : Type}
    (mf : M (A -> B)) (ma : M A) : M B :=
        mf >>= fun f => ma >>= fun a => ret (f a).

Fixpoint filterM {M : Type -> Type} {_xd : Monad M} {A : Type}
    (f : A -> M bool) (l : list A) : M (list A) :=
match l with
    | [] => ret []
    | h :: t => f h >>= fun b : bool => if b
        then liftM2 (@cons A) (ret h) (filterM f t)
        else filterM f t
end.
Require Import List.

Fixpoint sequence {M : Type -> Type} {_xd : Monad M} {A : Type}
    (lma : list (M A)) : M (list A) :=
match lma with
    | [] => ret []
    | h :: t => liftM2 (@cons A) h (sequence t)
end.

Section MonadWut.

Variable M : Type -> Type.
Variable inst : Monad M.

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

(* Fixpoint zipWithM {A B C : Type} (f : A -> B -> M C) (la : list A) (lb : list B)
    : M (list C) :=
match la, lb with
    | [], _ => ret []
    | _, [] => ret []
    | ha :: ta, hb :: tb =>
        f ha hb >>= fun c : C =>
        zipWithM f ta tb >>= fun cs : list C =>
        ret (c :: cs)
end. *)

Definition when (b : bool) (mu : M unit) : M unit :=
match b with
    | true => mu
    | false => ret tt
end.

Definition unless (b : bool) (mu : M unit) : M unit :=
    when (negb b) mu.

Definition discard {A B : Type} (_ : M A) (mb : M B) : M B := mb.

Notation "ma >> mb" := (discard ma mb) (at level 40).


End MonadWut.

Check zipWithM.