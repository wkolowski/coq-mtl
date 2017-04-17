Inductive sigM {A : Type} (P : A -> Prop) : Type -> Type :=
    | existM : forall x : A, P x -> sigM P A.

Arguments sigM [A] _ _.
Arguments existM [A] _ _ _.

Notation "{ x : A | P }" := (sigM (fun x => P) A) : type_scope.

Eval compute in {x : nat | x = 5}.
Eval compute in (existM (fun n => n = 5) 5 eq_refl).

Definition comp_sigM {A B C : Type} {P : B -> Prop} {Q : C -> Prop}
    (f : A -> {x : B | P x}) (g : B -> {x : C | Q x}) (a : A) : {x : C | Q x} :=
match f a with
    | existM b _ => g b
end.

Notation "f >=> g" := (comp_sigM f g) (at level 40).

Definition return_sigM {A : Type} (a : A) : sigM (fun a : A => True) A :=
    existM (fun a : A => True) a I.

(*Theorem sig_id_left : forall (A B : Type) (P : B -> Prop)
    (f : A -> {x : B | P x}), f >=> return_sigM = f.*)

Definition coreturn_sigM {A : Type} {P : A -> Prop} (ma : {a : A | P a}) : A :=
match ma with
    | existM a _ => a
end.

Definition bind_sigM {A B : Type} {P : A -> Prop} {Q : B -> Prop}
    (ma : {x : A | P x}) (f : A -> {x : B | Q x}) : {x : B | Q x} :=
match ma with
    | existM a p => f a
end.

(*Notation "x >>= f" := (bind_sigM x f) (at level 40).*)

Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Definition even_four : {n : nat | evenb n = true}.
Proof.
  refine (existM _ 4 _). auto.
Defined.

Fixpoint dbl_ind (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (HSS : forall n : nat, P n -> P (S (S n))) (n : nat) : P n :=
match n with
    | 0 => H0
    | 1 => H1
    | S (S n') => HSS n' (dbl_ind P H0 H1 HSS n')
end.

Definition double (n : nat) : {n : nat | evenb n = true}.
Proof.
  refine (existM _ (2 * n) _). induction n as [| | n'] using dbl_ind;
  simpl in *; auto. rewrite <- (plus_n_O n') in *.
  replace (n' + S (S n')) with (S (S (n' + n'))). auto.
  replace (n' + (S (S n'))) with (S (S n') + n'). auto.
  Require Import Arith. apply plus_comm.
Defined.

Notation "x >>= f" := (bind_sigM x f) (at level 40).

Hint Unfold double.
Eval compute in even_four >>= double.
Eval simpl in even_four >>= double.
Eval cbv delta beta iota zeta in even_four >>= double.

Definition join_sigM {A : Type} (P : A -> Prop) (Q : {x : A | P x} -> Prop)
    (s : {x : {a : A | P a} | Q x}) : {a : A | P a}.
Proof. destruct s. auto. Defined.

(* Too difficult. *)
(*Definition join_sigM_hard {A : Type} (P : A -> Prop) (Q : {x : A | P x} -> Prop)
    (s : {x : {a : A | P a} | Q x}) : {a : A | P a /\ forall
    H : P a, Q (existM P a H)}.
Proof. Print existM.
  destruct s as [x p]. 
match s with
    | existM (existM a p) q => existM P a (conj p q)
end. *)

Definition join_sigM' {A : Type} (P : A -> Prop) (Q : {x : A | P x} -> Prop)
    (s : {x : {a : A | P a} | Q x}) : {a : A | P a} := bind_sigM s id.

Theorem noneq_empty : forall (A B : Type) (P : A -> Prop),
    A <> B -> @sigM A P B -> False.
Proof.
  destruct 2; auto.
Qed.

Definition fmap_sigM {A : Type} {P : A -> Prop} (B C : Type) (f : B -> C)
    : {x : B | P x} -> @sigM C (fun _ => True) C.
Proof.
  destruct 1. exists (f x). auto.
Defined.

(*Instance Functor_sigM {A : Type} {P : A -> Prop} : Functor (sigM P) :=
{
    fmap := fun B C : Type => @fmap_sigM A P B C
}.*)

(* Monadic functions *)
(*Definition filterM {A : Type} {M : Type -> Type} {_ : Monad M}
    (p : A -> M bool) (l : list A) : M (list A) :=
match l with
    | [] => ret []
    | _ => ret []
end.*)

(*Inductive sigM' (A : Type) : Type :=
    | existM' : forall (P : A -> Prop) (x : A), P x -> sigM' A.

Instance Functor_sigM' : Functor sigM' :=
{
    fmap := fun {A B : Type} (f : A -> B) (p : sigM' A) =>
      match p with
        | existM' _ x _ => existM' (fun _ => True) (f x) I
      end
}.
Proof.
  intro. extensionality x. destruct x. simpl. unfold id.
*)
