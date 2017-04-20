Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Monoid.

Definition Writer (W : Monoid) (A : Type) : Type := prod A W.

Definition fmap_Writer {W : Monoid} {A B : Type} (f : A -> B) (wa : Writer W A)
    : Writer W B :=
match wa with
    | (a, w) => (f a, w)
end.

Definition ret_Writer {W : Monoid} {A : Type} (a : A) : Writer W A :=
    (a, neutr).

Definition ap_Writer {W : Monoid} {A B : Type} (wf : Writer W (A -> B))
    (wa : Writer W A) : Writer W B :=
match wf, wa with
    | pair f w, pair a w' => pair (f a) (op w w')
end.

Definition join_Writer {W : Monoid} {A : Type} (wwa : Writer W (Writer W A))
    : Writer W A :=
match wwa with
    | pair (pair a w) w' => pair a (op w w')
end.