Require Import Control.

Definition RWS (W : Monoid) (R S A : Type) : Type :=
  R -> S -> A * S * W.

Definition fmap_RWS
  {W : Monoid} {R S A B : Type}
  (f : A -> B) (x : RWS W R S A) : RWS W R S B :=
    fun r s =>
      let
        '(a, s', w) := x r s
      in
        (f a, s', w).

Hint Unfold RWS fmap_RWS : HSLib.

Instance Functor_RWS (W : Monoid) (R S : Type) : Functor (RWS W R S) :=
{
    fmap := @fmap_RWS W R S
}.
Proof. all: unfold compose; monad. Defined.

Definition pure_RWS {W : Monoid} {R S A : Type} (x : A) : RWS W R S A :=
  fun _ s => (x, s, neutr).

Definition ap_RWS
  {W : Monoid} {R S A B : Type}
  (f : RWS W R S (A -> B)) (x : RWS W R S A) : RWS W R S B :=
    fun r s => 
      let '(f', sf, wf) := f r s in
      let '(x', sx, wx) := x r sf in (f' x', sx, op wf wx). (*
      let '(x', sx, wx) := x r s in
      let '(f', sf, wf) := f r sx in (f' x', sf, op wx wf). *)

Hint Unfold pure_RWS ap_RWS : HSLib.

Instance Applicative_RWS
  (W : Monoid) (R S : Type) : Applicative (RWS W R S) :=
{
    is_functor := Functor_RWS W R S;
    pure := @pure_RWS W R S;
    ap := @ap_RWS W R S;
}.
Proof. all: monad. Defined.

Theorem RWS_not_CommutativeApplicative :
  ~ (forall (W : Monoid) (R S : Type),
      CommutativeApplicative _ (Applicative_RWS W R S)).
Proof.
  intro. destruct (H (Monoid_list_app bool) unit unit).
  unfold RWS in ap_comm.
  specialize (ap_comm nat nat nat (fun _ => id)
    (fun _ _ => (42, tt, [true; false]))
    (fun _ _ => (43, tt, [false; true]))).
  compute in ap_comm. do 2 apply (f_equal (fun f => f tt)) in ap_comm.
  inv ap_comm.
Qed.

Theorem RWS_not_Alternative :
  forall (W : Monoid) (R S : Type),
    R -> S -> Alternative (RWS W R S) -> False.
Proof.
  destruct 3. destruct (aempty False) as [[f _] _]; assumption. 
Qed.

Definition bind_RWS
  {W : Monoid} {R S A B : Type}
  (x : RWS W R S A) (f : A -> RWS W R S B) : RWS W R S B :=
    fun r s =>
      let '(x', sx, wx) := x r s in
      let '(b, sb, wb) := f x' r sx in (b, sb, op wx wb).

Hint Unfold bind_RWS : HSLib.

Instance Monad_RWS
  (W : Monoid) (R S : Type) : Monad (RWS W R S) :=
{
    is_applicative := Applicative_RWS W R S;
    bind := @bind_RWS W R S
}.
Proof. all: monad. Defined.