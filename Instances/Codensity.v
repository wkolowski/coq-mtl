Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.

Definition Codensity (A : Type) : Type :=
  forall {R : Type}, (A -> R) -> R.

Definition fmap_Codensity
  {A B : Type} (f : A -> B) (x : Codensity A) : Codensity B :=
    fun (R : Type) (y : B -> R) => x R (fun a : A => y (f a)).

Instance FunctorCodensity : Functor Codensity :=
{
    fmap := @fmap_Codensity
}.
Proof. all: reflexivity. Defined.

Definition ret_Codensity
  {A : Type} (a : A) : Codensity A :=
    fun (R : Type) (f : A -> R) => f a.

Definition ap_Codensity
  {A B : Type} (f : Codensity (A -> B)) (x : Codensity A) : Codensity B :=
    fun (R : Type) (y : B -> R) =>
      f R (fun h : A -> B => x R (fun a : A => y (h a))).

Instance Applicative_Codensity : Applicative Codensity :=
{
    is_functor := FunctorCodensity;
    ret := @ret_Codensity;
    ap := @ap_Codensity;
}.
Proof. all: reflexivity. Defined.

Definition bind_Codensity
  {A B : Type} (ca : Codensity A) (f : A -> Codensity B) : Codensity B :=
    fun (R : Type) (g : B -> R) => ca R (fun x : A => f x R g).

Theorem Codensity_not_Alternative :
  Alternative Codensity -> False.
Proof.
  destruct 1. unfold Codensity in *.
  apply (aempty False). intro. assumption.
Qed.

Require Import HSLib.MonadBind.Monad.

Instance MonadCodensity : Monad Codensity :=
{
    is_applicative := @Applicative_Codensity;
    bind := @bind_Codensity;
}.
Proof. all: reflexivity. Defined.

Lemma id_to_homotopy :
  forall (A : Type) (P : forall x : A, Type) (f g : forall x : A, P x),
    f = g -> forall x : A, f x = g x.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Instance CommutativeApplicative_Codensity
  : CommutativeApplicative _ Applicative_Codensity := {}.
Proof.
  intros. compute in *. ext R; ext y. f_equal.
Abort.

(* TODO: *) Theorem Codensity_not_CommutativeApplicative :
  ~ CommutativeApplicative _ Applicative_Codensity.
Proof.
  destruct 1. compute in *. Require Import Bool.
  specialize (
    ap_comm _ _ _ 
      (fun a b =>
      match a with
          | [] => b ++ b
          | _ => b ++ b ++ a
      end)
    (fun _ f => f [2]) (fun _ f => f [])). cbn in ap_comm.
  compute in ap_comm.
  Ltac ext_in H :=
  match type of H with
      | ?f = ?g =>
          match f with
              | (fun x : _ => _) => idtac x;
                  let x' := fresh x in
                  assert (forall x', f (let wut := x' in wut) = g x')
          end
(*      | ?f = ?g =>
          let H' := fresh "H" in
          assert (H' := @id_to_homotopy _ _ f g H);
          clear H; rename H' into H; cbn in H*)
  end. ext_in ap_comm.
  match goal with
      | H : ?f = ?g |- _ =>
          assert (f nat = g nat)
  end.
Abort. (* TODO: maybe Church encoding fo parsers? *)

Definition callCC_Type : Type :=
  forall A B : Type, ((A -> Codensity B) -> Codensity A) -> Codensity A.

(* TODO: why no callCC? *)
Theorem no_callCC :
  callCC_Type -> False.
Proof.
  unfold callCC_Type, Codensity. intro.
  apply (X nat False); intros.
    apply X1. exact 42.
    destruct H.
    
Abort.