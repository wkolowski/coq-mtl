Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition fmap_Cont {R A B : Type} (f : A -> B) (ca : Cont R A)
    : Cont R B := fun g : B -> R => ca (f .> g).

Definition ret_Cont {R A : Type} (a : A) : Cont R A :=
    fun f : A -> R => f a.

Definition ap_Cont {R A B : Type} (cf : Cont R (A -> B)) (ca : Cont R A)
    : Cont R B := fun br : B -> R => ca (fun a : A => cf (fun ab : A -> B =>
        br (ab a))).

Definition join_Cont {R A : Type} (cca : Cont R (Cont R A)) : Cont R A :=
    fun f : A -> R => cca (fun g : (A -> R) -> R => g f).