Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Variable char : Type.

Inductive Cmd (A : Type) : Type :=
    | GetChar : (char -> A) -> Cmd A
    | PutChar : char -> Cmd A.

Arguments GetChar [A] _.
Arguments PutChar [A] _.

Definition fmap_Cmd {A B : Type} (f : A -> B) (x : Cmd A) : Cmd B :=
match x with
    | GetChar  g => GetChar (fun c : char => f (g c))
    | PutChar c => PutChar c
end.

Theorem eta : forall (A B : Type) (f : A -> B),
    f = fun x : A => f x.
Proof. trivial. Qed.

Theorem eta_to_ext : forall (A B : Type) (f g : A -> B),
    (forall x : A, f x = g x) -> f = g.
Proof.
  intros. rewrite eta. rewrite (eta _ _ f).
Abort.

Instance FunctorCmd : Functor Cmd :=
{
    fmap := @fmap_Cmd
}.
Proof. (*Require Import FunctionalExtensionality.*)
  intros. unfold fmap_Cmd, id. extensionality x. destruct x.
    f_equal. trivial.
  intros. unfold fmap_Cmd, compose. extensionality x. destruct x; auto.
Qed.

