Require Import List.
Import ListNotations.

(** Monoids, represented as a class without any parameters. They are used
    by [Writer] and [Writert]. *)
Class Monoid : Type :=
{
    carr : Type;
    neutr : carr;
    op : carr -> carr -> carr;
    id_left :
      forall x : carr, op neutr x = x;
    id_right :
      forall x : carr, op x neutr = x;
    op_assoc :
      forall x y z : carr,
        op x (op y z) = op (op x y) z
}.

Coercion carr : Monoid >-> Sortclass.

Hint Rewrite @id_left @id_right @op_assoc : CoqMTL.

(** Some instances of monoids: the initial monoid, the monoid of boolean
    values with boolean conjunction and the monoid of lists with append. *)

#[refine]
Instance Monoid_unit : Monoid :=
{
    carr := unit;
    neutr := tt;
    op _ _ := tt
}.
Proof.
  all: try destruct x; reflexivity.
Defined.

#[refine]
Instance Monoid_bool_andb : Monoid :=
{
    carr := bool;
    neutr := true;
    op := andb;
}.
Proof.
  all: intros; repeat
  match goal with
      | b : bool |- _ => destruct b
  end; cbn; reflexivity.
Defined.

#[refine]
Instance Monoid_list_app (A : Type) : Monoid :=
{
    carr := list A;
    neutr := [];
    op := @app A;
}.
Proof.
  all: intros.
    reflexivity.
    rewrite app_nil_r. reflexivity.
    rewrite app_assoc. reflexivity.
Defined.