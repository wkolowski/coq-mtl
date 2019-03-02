Require Import Control.All.
Require Import Control.Monad.Class.All.

Require Import Misc.Monoid.

(** The optionality monad, known as Maybe in Haskell. *)
Definition Option (A : Type) : Type := option A.

Definition fmap_Option
  {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Hint Unfold fmap_Option : HSLib.

Instance Functor_Option : Functor option :=
{
    fmap := @fmap_Option
}.
Proof. all: monad. Defined.

Definition pure_Option := @Some.

Definition ap_Option
  {A B : Type} (of : option (A -> B)) (oa : option A) : option B :=
match of, oa with
    | Some f, Some a => Some (f a)
    | _, _ => None
end.

Hint Unfold pure_Option ap_Option : HSLib.

Instance Applicative_Option : Applicative option :=
{
    is_functor := Functor_Option;
    pure := pure_Option;
    ap := @ap_Option
}.
Proof. all: monad. Defined.

Definition aempty_Option {A : Type} : option A := None.

Definition aplus_Option {A : Type} (x y : option A) : option A :=
match x, y with
    | None, y => y
    | _, _ => x
end.

Hint Unfold aempty_Option aplus_Option : HSLib.

Instance Alternative_Option : Alternative option :=
{
    is_applicative := Applicative_Option;
    aempty := @aempty_Option;
    aplus := @aplus_Option
}.
Proof. all: monad. Defined.

Definition bind_Option 
  {A B : Type} (oa : option A) (f : A -> option B) : option B :=
match oa with
    | None => None
    | Some a => f a
end.

Hint Unfold bind_Option : HSLib.

Instance CommutativeApplicative_Option :
  CommutativeApplicative _ Applicative_Option.
Proof.
  split. monad.
Defined.

Instance Monad_Option : Monad option :=
{
    is_applicative := Applicative_Option;
    bind := @bind_Option
}.
Proof. all: monad. Defined.

Definition foldMap_Option
  {A : Type} {M : Monoid} (f : A -> M) (oa : option A) : M :=
match oa with
    | None => neutr
    | Some a => f a
end.

Hint Unfold foldMap_Option : HSLib.

Instance Foldable_Option : Foldable option :=
{
    foldMap := @foldMap_Option
}.
Proof. monad. Defined.

Definition fail_Option {A : Type} : option A := None.

Instance MonadFail_Option : MonadFail option Monad_Option :=
{
    fail := @fail_Option
}.
Proof. intros. compute. reflexivity. Defined.