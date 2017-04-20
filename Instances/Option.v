Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

(* option is already there, so we won't redefine it. *)

Definition fmap_Option {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Instance FunctorOption : Functor option :=
{
    fmap := @fmap_Option
}.
Proof.
  intros; extensionality x; destruct x; auto.
  intros; extensionality x; destruct x; auto.
Defined.

Definition ret_Option := Some.

Definition ap_Option {A B : Type} (of : option (A -> B)) (oa : option A)
    : option B :=
match of, oa with
    | Some f, Some a => Some (f a)
    | _, _ => None
end.

Instance ApplicativeOption : Applicative option :=
{
    is_functor := FunctorOption;
    ret := ret_Option;
    ap := @ap_Option
}.
Proof.
  intros. unfold id. destruct ax; trivial.
  intros. destruct ax, af, ag; trivial.
  intros. trivial.
  intros. destruct f; trivial.
Defined.

Definition aempty_Option {A : Type} : option A := None.

Definition aplus_Option {A : Type} (x y : option A) : option A :=
match x, y with
    | None, y => y
    | _, _ => x
end.

Instance AlternativeOption : Alternative option :=
{
    is_applicative := ApplicativeOption;
    aempty := @aempty_Option;
    aplus := @aplus_Option
}.
Proof.
  trivial.
  destruct fa; trivial.
  destruct x; try destruct y; try destruct z; trivial.
Defined.