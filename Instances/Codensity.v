Require Import Control.

Definition Codensity
  (F : Type -> Type) (A : Type) : Type :=
    forall {R : Type}, (A -> F R) -> F R.

Definition fmap_Codensity
  (F : Type -> Type) {A B : Type} (f : A -> B) (x : Codensity F A)
    : Codensity F B := fun (R : Type) (y : B -> F R) =>
      x R (fun a : A => y (f a)).

Instance FunctorCodensity
  (F : Type -> Type) : Functor (Codensity F) :=
{
    fmap := @fmap_Codensity F
}.
Proof. all: reflexivity. Defined.

Definition pure_Codensity
  (F : Type -> Type) {A : Type} (a : A) : Codensity F A :=
    fun (R : Type) (f : A -> F R) => f a.

Definition ap_Codensity
  (F : Type -> Type) {A B : Type} (f : Codensity F (A -> B))
  (x : Codensity F A) : Codensity F B :=
    fun (R : Type) (y : B -> F R) =>
      f R (fun h : A -> B => x R (fun a : A => y (h a))).

Instance Applicative_Codensity
  (F : Type -> Type) : Applicative (Codensity F) :=
{
    is_functor := FunctorCodensity F;
    pure := @pure_Codensity F;
    ap := @ap_Codensity F;
}.
Proof. all: reflexivity. Defined.

Definition bind_Codensity
  (F : Type -> Type) {A B : Type} (ca : Codensity F A) (f : A -> Codensity F B)
    : Codensity F B := fun (R : Type) (g : B -> F R) =>
      ca R (fun x : A => f x R g).

Theorem Codensity_not_Alternative :
  (forall F : Type -> Type, Alternative (Codensity F)) -> False.
Proof.
  intro H. destruct (H id). unfold Codensity in *.
  apply (aempty False). intro. assumption.
Qed.

Instance MonadCodensity
  (F : Type -> Type) : Monad (Codensity F) :=
{
    is_applicative := @Applicative_Codensity F;
    bind := @bind_Codensity F;
}.
Proof. all: reflexivity. Defined.

Lemma id_to_homotopy :
  forall (A : Type) (P : forall x : A, Type) (f g : forall x : A, P x),
    f = g -> forall x : A, f x = g x.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Instance CommutativeApplicative_Codensity
  (F : Type -> Type) : CommutativeApplicative _ (Applicative_Codensity F).
Proof.
  split. intros. compute in *. ext R; ext y. f_equal.
Abort.

(* Theorem Codensity_not_CommutativeApplicative :
  ~ CommutativeApplicative _ Applicative_Codensity.
Proof.
  destruct 1. compute in *. Require Import Bool.
  assert (
  forall (A B C : Type) (f : A -> B -> C)
         (u : forall R : Type, (A -> R) -> R)
         (v : forall R : Type, (B -> R) -> R),
         (fun (R : Type) (y : C -> R) =>
          u R (fun a : A => v R (f a .> y))) =
         (fun (R : Type) (y : C -> R) =>
          v R (fun b : B => u R (flip f b .> y)))).
  intros. unfold flip, compose. rewrite <- ap_comm. ext R; ext y.
    f_equal. clear H.
(*
  specialize (
    ap_comm nat bool unit).
  replace (fun a : nat => v R (fun a0 : bool => y (f a a0)))
  with (fun a : nat => v R (f a .> y)) in ap_comm.*)
  specialize (
    ap_comm _ _ _
      (fun a b =>
      match a ++ b with
          | [] => a ++ b ++ b
          | [1] => b ++ b ++ b
          | [2] => a ++ a ++ a
          | _ => []
      end)
    (fun _ f => f [2]) (fun _ f => f [1])). cbn in ap_comm.
  compute in ap_comm.
  Ltac ext_in H :=
  match type of H with
      | ?f = ?g =>
          match f with
              | (fun x : _ => _) => idtac x;
                  let x' := fresh x in
                  assert (forall x', f (let w := x' in w) = g x')
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
Abort. *)

(*
Definition callCC_Type : Type :=
  forall (F : Type -> Type) (A B : Type),
    ((A -> Codensity F B) -> Codensity F A) -> Codensity F A.

Require Import Instances.All.

Theorem no_callCC :
  callCC_Type -> False.
Proof.
  unfold callCC_Type, Codensity. intro.
  specialize (X Identity). unfold Identity in X.
  apply (X unit unit).
    firstorder.
    intros.
Restart.
  unfold callCC_Type, Codensity. intro.
  specialize (X option False False ltac:(firstorder)).
Restart.
  unfold callCC_Type, Codensity. intro.
  specialize (X (Writer Monoid_unit) unit False ltac:(firstorder)).
  specialize (X False). unfold Writer in X.
Restart.
  unfold callCC_Type, Codensity. intro.
  specialize (X (fun _ => unit)). cbn in X.
Abort.
*)

Section CodensityFuns.

Variable M : Type -> Type.
Variable inst : Monad M.

Definition inject
  {A : Type} (x : M A) : Codensity M A :=
    fun _ c => x >>= c.

Definition extract
  {A : Type} (x : Codensity M A) : M A := x _ pure.

Definition improve
  {A : Type} (x : M A) : M A :=
    extract (inject x).

Hint Unfold
  Codensity fmap_Codensity pure_Codensity ap_Codensity bind_Codensity
  inject extract : HSLib.

Lemma extract_pure :
  forall (A : Type) (x : A),
    extract (pure x) = pure x.
Proof. monad. Qed.

Lemma extract_pure' :
  forall (A : Type) (x : M A),
    extract (fun _ c => x >>= c) = x.
Proof. monad. Qed.

Lemma extract_inject :
  forall (A : Type) (x : M A),
    extract (inject x) = x.
Proof. monad. Qed.

Lemma improve_spec :
  forall (A : Type) (x : M A),
    improve x = x.
Proof. apply extract_inject. Qed.

Lemma inject_extract :
  forall (A : Type) (x : Codensity M A),
    inject (extract x) = x.
Proof.
  intros. unfold inject, extract. ext2 R c.
  unfold Codensity in *.
  
Abort.

End CodensityFuns.

Arguments improve {M inst A } _.

Require Import MonadClass.MonadFree.

Print MonadFree.

Definition wrap_Codensity
  {F M : Type -> Type} {instF : Functor F} {instM : Monad M}
  {instMF : MonadFree F M instF instM} {A : Type}
  (x : F (Codensity M A)) : Codensity M A :=
    fun R g => wrap (fmap (fun f => f R g) x).

Hint Unfold
  Codensity fmap_Codensity pure_Codensity ap_Codensity bind_Codensity
  wrap_Codensity : HSLib.

Instance MonadFree_Free
  {F M : Type -> Type} {instF : Functor F} {instM : Monad M}
  {instMF : MonadFree F M instF instM}
  : MonadFree F (Codensity M) instF (MonadCodensity M) :=
{
    wrap := @wrap_Codensity F M instF instM instMF
}.
Proof.
  monad. rewrite <- !fmap_comp'. unfold compose. reflexivity.
Defined.