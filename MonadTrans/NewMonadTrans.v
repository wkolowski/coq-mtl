Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadJoin.Monad.
Require Import HSLib.MonadJoin.MonadInst.

Require Import HSLib.Instances.Option.

Class MonadTrans (T : (Type -> Type) -> Type -> Type) : Type :=
{
    lift : forall {M : Type -> Type} {_inst : Monad M} {A : Type},
        M A -> T M A;
    is_monad : forall (M : Type -> Type), Monad M -> Monad (T M);
    law : forall (M : Type -> Type) {_inst : Monad M} (A : Type),
        forall x : A, ret x = lift (ret x)
}.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Instance FunctorOptionT (M : Type -> Type) {_inst : Functor M}
    : Functor (OptionT M) :=
{
    fmap := fun (A B : Type) (f : A -> B) =>
      (*@fmap option FunctorOption A B .> @fmap M _inst (option A) (option B)*)
      @fmap M _inst _ _ (@fmap option FunctorOption A B f)
}.
Proof.
  intros. unfold compose. do 2 rewrite fmap_pres_id. trivial.
  intros. unfold compose. replace (fun x : A => g (f x)) with (f .> g); auto.
    do 2 rewrite fmap_pres_comp. extensionality x. unfold compose. trivial.
Defined.

(*Require Import Applicative.

Instance ApplicativeOptionT (M : Type -> Type) {_inst : Applicative M}
    : Applicative (OptionT M) :=
{
    is_functor := @FunctorOptionT M _inst;
    ret := fun (A : Type) (x : A) => ret (Some x);
    ap := fun (A B : Type) => @liftA2 M _inst _ _ _ ap
}.
Proof.
  intros. 
    
  Focus 3. intros. unfold liftA2. do 2 rewrite homomorphism. simpl. trivial.
  Focus 3. intros. unfold liftA2.
    (*rewrite homomorphism. Print Applicative. repeat rewrite <- homomorphism.*)
    repeat rewrite interchange, homomorphism.
    repeat rewrite <- interchange, <- homomorphism. 
    repeat rewrite interchange, homomorphism.
    repeat rewrite <- interchange, <- homomorphism.
Abort.*)

Definition OptionT_join {A : Type} {M : Type -> Type} {inst : Monad M}
    (moma : OptionT M (OptionT M A)) : OptionT M A.
Proof.
  red. red in moma. refine (moma >>= fun oma =>
  match oma with
      | None => ret None
      | Some ma => ma
  end).
Defined.

(*Definition OptionT_bind {A B : Type} {M : Type -> Type} {inst : Monad M}
    (moa : OptionT M A) (f : A -> OptionT M B)
    : OptionT M B := moa >>= fun oa : option A =>
match oa with
    | None => ret None
    | Some a => f a
end.*)

Instance MonadOptionT (M : Type -> Type) {inst : Monad M}
    : Monad (OptionT M) :=
{
    is_functor := FunctorOptionT M;
    ret := fun (A : Type) (x : A) => ret (Some x);
    join := fun (A : Type) => @OptionT_join A M inst
}.
Proof.
  simpl.
  Focus 2.
    intro. extensionality x. unfold OptionT_join.
    unfold compose. unfold bind.
Abort.


(*Definition bind_MonadTrans_option {A B : Type} (M : Type -> Type) {xd : Monad M}
    (moa : M (option A)) (f : A -> M (option B)) : M (option B) :=
    moa >>= fun oa : option A => match oa with
      | None => ret None
      | Some a => f a
    end.*)

(*Definition MonadTransOptionT_join (M : Type -> Type) {_inst : Monad M}
    (A : Type) (x : M (option (M (option A)))) : M (option A) :=
    x >>= fun omoa : option (M (option A)) =>
    match omoa with
      | None => ret None
      | Some moa => moa
    end.*)

(*Instance MonadTrans_option_is_monad (M : Type -> Type) {_inst : Monad M}
    : Monad (OptionT M) :=
{
    ret := fun (A : Type) (a : A) => ret (Some a);
    join := @MonadTransOptionT_join M _inst;
    is_functor := MonadTransOptionT_is_functor M
}.
Proof.*)

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

(*Instance MonadTransOption : MonadTrans OptionT :=
{
    lift := fun (M : Type -> Type) _ (A : Type) (ma : M A) =>
        ma >>= fun a => ret (Some a)
}.
Proof.
  intros.*)