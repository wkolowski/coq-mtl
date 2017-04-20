Require Import Applicative.
Require Import ApplicativeInst.

Class Alternative (F : Type -> Type) : Type :=
{
    is_applicative :> Applicative F;
    aempty : forall {A : Type}, F A;
    aplus : forall {A : Type}, F A -> F A -> F A;
    id_left : forall (A : Type) (fa : F A),
        aplus aempty fa = fa;
    id_right : forall (A : Type) (fa : F A),
        aplus fa aempty = fa;
    aplus_assoc : forall (A : Type) (x y z : F A),
        aplus x (aplus y z) = aplus (aplus x y) z
}.

(*Instance AlternativeOption : Alternative option :=
{
    is_applicative := ApplicativeOption;
    aempty := fun _ => None;
    aplus := fun (A : Type) (x y : option A) =>
        match x, y with
            | None, y => y
            | _, _ => x
        end
}.
Proof.
  trivial.
  destruct fa; trivial.
  destruct x; try destruct y; try destruct z; trivial.
Defined.

Instance AlternativeList : Alternative list :=
{
    is_applicative := ApplicativeList;
    aempty := fun _ => [];
    aplus := app
}.
Proof.
  apply app_nil_l.
  apply app_nil_r.
  apply app_assoc.
Defined.

Definition guard {F : Type -> Type} {_inst : Alternative F} {A : Type}
    (b : bool) : F unit := if b then ret tt else aempty.



*)