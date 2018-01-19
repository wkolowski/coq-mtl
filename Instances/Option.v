Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

(* option is already there, so we won't redefine it. *)

Definition fmap_Option
  {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Instance FunctorOption : Functor option :=
{
    fmap := @fmap_Option
}.
Proof.
  all: intros; ext x; destruct x; auto.
Defined.

Definition ret_Option := @Some.

Definition ap_Option
  {A B : Type} (of : option (A -> B)) (oa : option A) : option B :=
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
  all: intros; repeat
  match goal with
      | x : option _ |- _ => destruct x
  end; compute; reflexivity.
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
  all: intros; repeat
  match goal with
      | x : option _ |- _ => destruct x
  end; cbn; reflexivity.
Defined.

Definition join_Option
  {A : Type} (ooa : option (option A)) : option A :=
match ooa with
    | Some (Some x) => Some x
    | _ => None
end.

Definition bind_Option 
  {A B : Type} (oa : option A) (f : A -> option B) : option B :=
match oa with
    | None => None
    | Some a => f a
end.

Definition compM_Option
  {A B C : Type} (f : A -> option B) (g : B -> option C) (a : A) : option C :=
match f a with
    | None => None
    | Some b => g b
end.

Instance CommutativeApplicative_Option :
  CommutativeApplicative _ ApplicativeOption.
Proof.
  split. destruct u, v; compute; reflexivity.
Qed.