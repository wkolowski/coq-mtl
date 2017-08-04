Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadJoin.Monad.
(*Require Import MonadTrans.*)

Require Import HSLib.Instances.Option.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Section wut.

Variable M : Type -> Type.
Variable inst : Monad M.
Variables A B C : Type.

Definition OptionT_fmap (*{M : Type -> Type} {inst : Monad M} {A B : Type}*)
    (f : A -> B) (x : OptionT M A) : OptionT M B :=
    fmap (fmap f) x.

Definition OptionT_bind
    (moa : M (option A)) (f : A -> M (option B)) : M (option B) :=
    moa >>= fun oa : option A => match oa with
      | None => ret None
      | Some a => f a
    end.

Definition OptionT_join
    (x : M (option (M (option A)))) : M (option A) :=
    x >>= fun omoa : option (M (option A)) =>
    match omoa with
      | None => ret None
      | Some moa => moa
    end.

End wut.

Instance FunctorOptionT (M : Type -> Type) (inst : Monad M)
    : Functor (OptionT M) :=
{
    fmap := @OptionT_fmap M inst
}.
Proof.
  intro. unfold compose, OptionT_fmap. do 2 rewrite fmap_pres_id. trivial.
  intros. unfold compose, OptionT_fmap.
    replace (fun x : A => g (f x)) with (f .> g); auto.
      extensionality x. do 2 rewrite fmap_pres_comp. auto.
Defined.

Instance MonadOptionT (M : Type -> Type) {inst : Monad M}
    : Monad (OptionT M) :=
{
    is_functor := FunctorOptionT M inst;
    ret := fun (A : Type) (a : A) => ret (Some a);
    join := @OptionT_join M inst
}.
Proof.
  Focus 2. intro.
Abort.