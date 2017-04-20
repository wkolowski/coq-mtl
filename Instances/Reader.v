Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Import HSLib.Base.

Definition Reader (R A : Type) : Type := R -> A.

Definition fmap_Reader {R A B : Type} (f : A -> B)
    (ra : Reader R A) : Reader R B :=
    fun r : R => f (ra r).

Definition ret_Reader {R A : Type} (a : A) : Reader R A :=
    fun _ : R => a.

Definition ap_Reader {R A B : Type} (f : Reader R (A -> B)) (ra : Reader R A)
    : Reader R B := fun r : R => f r (ra r).

Definition join_Reader {R A : Type} (rra : Reader R (Reader R A))
    : Reader R A := fun r : R => rra r r.