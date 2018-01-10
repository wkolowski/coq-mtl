Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.Functor.Functor.
Require Export HSLib.Applicative.Applicative.

(* Definition of monad using ret and join. *)
Class Monad (M : Type -> Type) : Type :=
{
    is_applicative :> Applicative M;
    join : forall {A : Type}, M (M A) -> M A;
    join_law :
      forall (X : Type),
        fmap join .> join = join .> @join X;
    ret_law :
      forall (X : Type),
        ret .> join = fmap ret .> @join X;
    join_ret :
      forall (A : Type) (ma : M A), join (ret ma) = ma
}.

Coercion is_applicative : Monad >-> Applicative.

Definition bind
  {A B : Type} {M : Type -> Type} {inst : Monad M} (ma : M A) (f : A -> M B)
    : M B := (fmap f .> join) ma.

Definition bind_
  {M : Type -> Type} {_ : Monad M} {A B : Type} (ma : M A) (mb : M B)
    : M B := bind ma (fun _ => mb).

Definition compM
  {A B C : Type} {M : Type -> Type} {inst : Monad M}
  (f : A -> M B) (g : B -> M C) : A -> M C :=
    f .> fmap g .> join.

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

End DerivedLaws. (* TODO *)