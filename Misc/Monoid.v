Require Import Base.

Class Monoid : Type :=
{
    carr :> Type;
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

Hint Rewrite @id_left @id_right @op_assoc : HSLib.

Instance Monoid_unit : Monoid :=
{
    carr := unit;
    neutr := tt;
    op _ _ := tt
}.
Proof.
  all: try destruct x; reflexivity.
Defined.

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