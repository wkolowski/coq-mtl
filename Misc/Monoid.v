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