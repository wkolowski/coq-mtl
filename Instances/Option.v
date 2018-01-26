Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Functor.
Require Import Control.Applicative.
Require Import Control.Alternative.
Require Import Control.Monad.
Require Import Control.MonadPlus.

(* option is already there, so we won't redefine it. *)

Definition Option (A : Type) : Type := option A.

Definition fmap_Option
  {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Hint Unfold Option fmap_Option : HSLib.

Instance FunctorOption : Functor option :=
{
    fmap := @fmap_Option
}.
Proof.
  all: monad.
Defined.

Definition ret_Option := @Some.

Definition ap_Option
  {A B : Type} (of : option (A -> B)) (oa : option A) : option B :=
match of, oa with
    | Some f, Some a => Some (f a)
    | _, _ => None
end.

Hint Unfold ret_Option ap_Option : HSLib.

Instance ApplicativeOption : Applicative option :=
{
    is_functor := FunctorOption;
    ret := ret_Option;
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

Instance AlternativeOption : Alternative option :=
{
    is_applicative := ApplicativeOption;
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
  CommutativeApplicative _ ApplicativeOption.
Proof.
  split. destruct u, v; compute; reflexivity.
Qed.

Instance MonadOption : Monad option :=
{
    is_applicative := ApplicativeOption;
    bind := @bind_Option
}.
Proof. all: monad. Defined.