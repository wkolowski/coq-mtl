Require Import List.
Import ListNotations.

(** Monoids, represented as a class without any parameters. They are used
    by [Writer] and [WriterT]. *)
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

#[global] Hint Rewrite @id_left @id_right @op_assoc : CoqMTL.

(** Some instances of monoids: the initial monoid, the monoid of boolean
    values with boolean conjunction and the monoid of lists with append. *)

#[refine]
#[export]
Instance Monoid_unit : Monoid :=
{
  carr := unit;
  neutr := tt;
  op _ _ := tt
}.
Proof.
  all: now intros [].
Defined.

#[refine]
#[export]
Instance Monoid_bool_andb : Monoid :=
{
  carr := bool;
  neutr := true;
  op := andb;
}.
Proof.
  all: now intros []; cbn.
Defined.

#[refine]
#[export]
Instance Monoid_list_app (A : Type) : Monoid :=
{
  carr := list A;
  neutr := [];
  op := @app A;
}.
Proof.
  - reflexivity.
  - now intros; rewrite app_nil_r.
  - now intros; rewrite app_assoc.
Defined.