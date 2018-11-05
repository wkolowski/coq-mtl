Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.
Require Import Control.MonadTrans.

(* TODO: find out wut's up with commutative monads *)

Definition ListT
  (M : Type -> Type) (A : Type) : Type :=
    forall X : Type, M X -> (A -> M X -> M X) -> M X.

(* Modified version of list notations from standard library. *)
Module ListT_Notations.

Notation "[[ ]]" :=
  (fun X nil _ => nil).
Notation "[[ x ]]" :=
  (fun X nil cons => cons x nil).
Notation "[[ x ; y ; .. ; z ]]" :=
  (fun X nil cons => cons x (cons y .. (cons z nil) ..)).
(* BEWARE: Compatibility with 8.4 not supported in 8.8.1
Notation "[[ x ; .. ; y ]]" :=
  (fun X nil cons => cons x .. (cons y nil) ..) (compat "8.4").
*)

End ListT_Notations.

Export ListT_Notations.

Definition fmap_ListT
  {M : Type -> Type} {inst : Functor M} {A B : Type}
  (f : A -> B) (l : ListT M A) : ListT M B :=
    fun (X : Type) (nil : M X) (cons : B -> M X -> M X) =>
      l X nil (fun h t => cons (f h) t).

Instance Functor_ListT
  (M : Type -> Type) (inst : Functor M) : Functor (ListT M) :=
{
    fmap := @fmap_ListT M inst
}.
Proof. all: hs. Defined.

Definition pure_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (x : A) : ListT M A :=
    fun (X : Type) (nil : M X) (cons : A -> M X -> M X) => cons x nil.

Definition ap_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mfs : ListT M (A -> B)) (mxs : ListT M A) : ListT M B :=
    fun X nil cons =>
      mfs X nil (fun f fs => fmap f mxs X fs cons).

Global Instance Applicative_ListT
  (M : Type -> Type) (inst : Monad M) : Applicative (ListT M) :=
{
    is_functor := Functor_ListT M inst;
    pure := @pure_ListT M inst;
    ap := @ap_ListT M inst;
}.
Proof. all: hs. Defined.

Definition aempty_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) : ListT M A :=
    fun X nil cons => nil.

Definition aplus_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (ml1 ml2 : ListT M A)
    : ListT M A := fun X nil cons => ml1 X (ml2 X nil cons) cons.

Instance Alternative_ListT
  (M : Type -> Type) (inst : Monad M) : Alternative (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    aempty := aempty_ListT M inst;
    aplus := aplus_ListT M inst;
}.
Proof. all: hs. Defined.

Definition bind_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mla : ListT M A) (f : A -> ListT M B) : ListT M B :=
    fun X nil cons => mla X nil (fun h t => f h X t cons).

Instance Monad_ListT
  (M : Type -> Type) (inst : Monad M) : Monad (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    bind := @bind_ListT M inst
}.
Proof. all: hs. Defined.

Instance MonadPlus_ListT
  (M : Type -> Type) (inst : Monad M) : MonadPlus (ListT M) :=
{
    is_monad := Monad_ListT _ inst;
    is_alternative := Alternative_ListT _ inst;
}.
Proof. hs. Defined.

Definition lift_ListT
  {M : Type -> Type} {inst : Monad M} (A : Type) (ma : M A) : ListT M A :=
    fun X nil cons => ma >>= fun a : A => cons a nil.

Hint Unfold pure_ListT bind_ListT lift_ListT : HSLib.

Instance MonadTrans_ListT : MonadTrans ListT :=
{
    is_monad := @Monad_ListT;
    lift := @lift_ListT;
}.
Proof. all: monad. Defined.