From CoqMTL Require Import Control.All.
From CoqMTL Require Import Control.Monad.Identity.
From CoqMTL Require Import Control.Monad.Class.MonadFree.

(** The codensity monad. Not very developed, as I don't know too much
    about it. In particular, I didn't check if it really improves
    asymptotic complexity or even performance, as this is quite hard
    in Coq, where everything is rather slow. *)
Definition Codensity
  (F : Type -> Type) (A : Type) : Type :=
    forall (R : Type), (A -> F R) -> F R.

Definition fmap_Codensity
  (F : Type -> Type) {A B : Type} (f : A -> B) (x : Codensity F A)
    : Codensity F B := fun (R : Type) (y : B -> F R) =>
      x R (fun a : A => y (f a)).

#[refine]
#[export]
Instance Functor_Codensity
  (F : Type -> Type) : Functor (Codensity F) :=
{
  fmap := @fmap_Codensity F;
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

#[refine]
#[export]
Instance Applicative_Codensity
  (F : Type -> Type) : Applicative (Codensity F) :=
{
  is_functor := Functor_Codensity F;
  pure := @pure_Codensity F;
  ap := @ap_Codensity F;
}.
Proof. all: reflexivity. Defined.

Definition bind_Codensity
  (F : Type -> Type) {A B : Type}
  (ca : Codensity F A) (f : A -> Codensity F B)
    : Codensity F B := fun (R : Type) (g : B -> F R) =>
      ca R (fun x : A => f x R g).

Theorem Codensity_not_Alternative :
  (forall F : Type -> Type, Alternative (Codensity F)) -> False.
Proof.
  intro H. destruct (H id). unfold Codensity in *.
  apply (aempty False). intro. assumption.
Qed.

#[refine]
#[export]
Instance Monad_Codensity
  (F : Type -> Type) : Monad (Codensity F) :=
{
  is_applicative := @Applicative_Codensity F;
  bind := @bind_Codensity F;
}.
Proof. all: reflexivity. Defined.

(** Since [Codensity] is somewhat akin to [Free], we shouldn't expect
    it to be commutative. *)
Lemma Codensity_not_CommutativeApplicative :
  (forall F : Type -> Type,
    CommutativeApplicative _ (Applicative_Codensity F)) -> False.
Proof.
  intros.
  specialize (H list).
  destruct H. cbn in *. compute in *.
  specialize (ap_comm bool bool bool (fun a b => andb a b)). cbn in *.
  specialize (ap_comm (fun R f => f false ++ f true)
                      (fun _ f => f true ++ f false)).
  cbn in *.
  apply (f_equal (fun f => f bool)) in ap_comm.
  apply (f_equal (fun f => f (fun b => [b]))) in ap_comm.
  cbn in ap_comm. inv ap_comm.
Qed.

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
  fmap_Codensity pure_Codensity ap_Codensity bind_Codensity inject extract
  : CoqMTL.

Lemma extract_pure :
  forall (A : Type) (x : A),
    extract (pure x) = pure x.
Proof. monad. Qed.

Lemma extract_pure' :
  forall (A : Type) (x : M A),
    extract (fun _ c => x >>= c) = x.
Proof. monad. Qed.

(** Does inject (extract x) = x hold? Probably not, but not sure. *)
Lemma extract_inject :
  forall (A : Type) (x : M A),
    extract (inject x) = x.
Proof. monad. Qed.

Lemma improve_spec :
  forall (A : Type) (x : M A),
    improve x = x.
Proof. apply extract_inject. Qed.

End CodensityFuns.

Arguments improve {M inst A } _.

Definition wrap_Codensity
  {F M : Type -> Type} {instF : Functor F} {instM : Monad M}
  {instMF : MonadFree F M instF instM} {A : Type}
  (x : F (Codensity M A)) : Codensity M A :=
    fun R g => wrap (fmap (fun f => f R g) x).

#[global] Hint Unfold
  fmap_Codensity pure_Codensity ap_Codensity bind_Codensity
  wrap_Codensity : CoqMTL.

#[refine]
#[export]
Instance MonadFree_Codensity
  {F M : Type -> Type} {instF : Functor F} {instM : Monad M}
  {instMF : MonadFree F M instF instM}
  : MonadFree F (Codensity M) instF (Monad_Codensity M) :=
{
  wrap := @wrap_Codensity F M instF instM instMF;
}.
Proof.
  hs. ext2 R g. rewrite <- !fmap_comp'. unfold compose. reflexivity.
Defined.

(** I was wondering whether [Codensity] could in theory support callCC,
    because in http://comonad.com/reader/2011/free-monads-for-less/
    Edawrd Kmett states that it doesn't, so I went on to check this.
    The first type is of the usual callCC (with [Cont] replaced by
    [Codensity]) and the second one is taken from Purescript's
    Pursuit library. *)

Definition callCC_Type : Type :=
  forall (F : Type -> Type) (A B : Type),
    ((A -> Codensity F B) -> Codensity F A) -> Codensity F A.

Definition callCC'_Type : Type :=
  forall (F : Type -> Type) (A : Type),
    ((forall B : Type, A -> Codensity F B) ->
        Codensity F A) -> Codensity F A.

(** It turns out that when we use excluded middle for [Type], we can
    define both versions of callCC. This proves that [Codensity] does
    not forbid callCC. However, I think that there's no way to define
    it constructively. *)

Lemma calCC_classic :
  (forall A : Type, A + (A -> False)) -> callCC_Type.
Proof.
  unfold callCC_Type. intros LEM F A B H.
  destruct (LEM (Codensity F A)).
  - assumption.
  - apply H. intro. cut False.
    + inversion 1.
    + apply f. red. intros. apply X0. assumption.
Qed.

Lemma calCC'_classic :
  (forall A : Type, A + (A -> False)) -> callCC'_Type.
Proof.
  unfold callCC'_Type. intros LEM F A H.
  destruct (LEM (Codensity F A)).
  - assumption.
  - apply H. intros B a. cut False.
    + inversion 1.
    + apply f. red. intros. apply X. assumption.
Qed.