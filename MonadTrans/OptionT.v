Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadJoin.Monad.
Require Import HSLib.MonadJoin.MonadInst.
Require Import MonadTrans.

Require Import HSLib.Instances.Option.

Instance MonadTrans_option_is_functor (M : Type -> Type) {xd : Monad M}
    : Functor (fun A : Type => M (option A)) :=
{
    fmap := fun (A B : Type) =>
      @fmap option FunctorOption A B .> @fmap M xd (option A) (option B)
}.
Proof.
  intro. unfold compose. do 2 rewrite fmap_pres_id. trivial.
  intros. unfold compose. replace (fun x : A => g (f x)) with (f .> g); auto.
    extensionality x. do 2 rewrite fmap_pres_comp. auto.
Defined.

Definition bind_MonadTrans_option
    (M : Type -> Type) {_ : Monad M} {A B : Type}
    (moa : M (option A)) (f : A -> M (option B)) : M (option B) :=
    moa >>= fun oa : option A => match oa with
      | None => ret None
      | Some a => f a
    end.

Definition MonadTrans_option_join (M : Type -> Type) {xd : Monad M}
    (A : Type) (x : M (option (M (option A)))) : M (option A) :=
    x >>= fun omoa : option (M (option A)) =>
    match omoa with
      | None => ret None
      | Some moa => moa
    end.

Instance MonadTrans_option_is_monad (M : Type -> Type) {xd : Monad M}
    : Monad (fun A : Type => M (option A)) :=
{
    ret := fun (A : Type) (a : A) => ret (Some a);
    join := @MonadTrans_option_join M xd;
    is_functor := MonadTrans_option_is_functor M
}.
Abort.

(*Instance MonadTrans_option_is_functor' (M : Type -> Type) {xd : Monad M}
    : Functor (fun A : Type => option (M A)) :=
{
    fmap := fun (A B : Type) =>
        @fmap M xd A B .> @fmap option FunctorOption (M A) (M B)
}.
Proof.
  intro. unfold compose. do 2 rewrite fmap_pres_id. trivial.
  intros. unfold compose. simpl. extensionality x.
    destruct x; auto. f_equal. replace (fun x : A => g (f x)) with (f .> g).
      rewrite fmap_pres_comp. unfold compose. trivial.
      auto.
Defined.*)

Instance MonadTrans_option : MonadTrans option :=
{
    lift := fun (M : Type -> Type) {_ : Monad M} (A : Type)
        (ma : M A) => ma >>= fun a : A => ret (Some a)
}.
Abort.

(*Check @lift.
Eval compute in @lift option MonadTrans_option list MonadList nat [5].
Check lift.
Eval compute in lift option [5].*)
