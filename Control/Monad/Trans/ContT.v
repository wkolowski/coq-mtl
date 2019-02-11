Require Import Control.

Definition ContT (R : Type) (M : Type -> Type) (A : Type)
  : Type := (A -> M R) -> M R.

Section ContT_instances.

Variables
  (R : Type)
  (M : Type -> Type)
  (inst : Monad M).

Definition fmap_ContT
  (A B : Type) (f : A -> B) (x : ContT R M A) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => y (f a)).

Instance FunctorContT : Functor (ContT R M) :=
{
    fmap := fmap_ContT
}.
Proof. all: hs. Defined.

Definition pure_ContT (A : Type) (x : A) : ContT R M A :=
  fun y : A -> M R => y x.

Definition ap_ContT
  (A B : Type) (mf : ContT R M (A -> B)) (ma : ContT R M A) : ContT R M B :=
    fun y : B -> M R => mf (fun f : A -> B => ma (fun a : A => y (f a))).

Instance ApplicativeContT : Applicative (ContT R M) :=
{
    is_functor := FunctorContT;
    pure := pure_ContT;
    ap := ap_ContT;
}.
Proof. all: reflexivity. Defined.

Definition bind_ContT
  (A B : Type) (x : ContT R M A) (f : A -> ContT R M B) : ContT R M B :=
    fun y : B -> M R => x (fun a : A => f a y).

Instance Monad_ContT : Monad (ContT R M) :=
{
    is_applicative := ApplicativeContT;
    bind := bind_ContT;
}.
Proof. all: reflexivity. Defined.

Definition lift_ContT
  (A : Type) (ma : M A) : ContT R M A :=
    fun y : A -> M R => @bind M inst _ _ ma (fun a : A => y a).

End ContT_instances.

Hint Unfold
  ContT fmap_ContT pure_ContT ap_ContT bind_ContT lift_ContT : HSLib.

Instance MonadTrans_ContT (R : Type) : MonadTrans (ContT R) :=
{
    is_monad := fun M _ => @Monad_ContT R M;
    lift := @lift_ContT R;
}.
Proof. all: monad. Defined.

Require Import Control.Monad.Class.All.

Instance MonadAlt_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (ContT R M) (Monad_ContT R M) :=
{
    choose :=
      fun A x y k => choose (x k) (y k)
}.
Proof.
  intros. ext k. rewrite choose_assoc. reflexivity.
  intros. ext k. cbn. reflexivity.
Defined.

Instance MonadFail_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (ContT R M) (Monad_ContT R M) :=
{
    fail := fun A k => fail >>= k
}.
Proof.
(*  Hint Unfold fail : HSLib.*)
  intros. cbn. monad. rewrite !bind_fail_l. reflexivity.
Defined.

Instance MonadNondet_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (ContT R M) (Monad_ContT R M) :=
{
    instF := @MonadFail_ContT R M inst (@instF _ _ inst');
    instA := @MonadAlt_ContT R M inst (@instA _ _ inst');
}.
Proof.
  intros. cbn. ext k. rewrite bind_fail_l, choose_fail_l. reflexivity.
  intros. cbn. ext k. rewrite bind_fail_l, choose_fail_r. reflexivity.
Defined.

(* TODO *) Instance MonadExcept_ContT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (ContT R M) (Monad_ContT R M) :=
{
    instF := @MonadFail_ContT R M inst inst';
    catch := fun A x y k => catch (x k) (y k);
}.
Proof.
  all: intros; ext k; cbn.
    rewrite bind_fail_l, catch_fail_l. reflexivity.
    rewrite bind_fail_l, catch_fail_r. reflexivity.
    rewrite catch_assoc. reflexivity.
    unfold pure_ContT. Print MonadExcept.
Abort.

Instance MonadReader_ContT
  (E R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (ContT R M) (Monad_ContT R M) :=
{
    ask := fun k => ask >>= k
}.
Proof.
  rewrite constrA_spec. cbn. unfold bind_ContT. ext e.
  rewrite <- constrA_spec, constrA_bind_assoc, ask_ask. reflexivity.
Defined.

Instance MonadState_ContT
  (S R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (ContT R M) (Monad_ContT R M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  all: intros.
    rewrite constrA_spec. cbn. unfold bind_ContT. ext u.
      rewrite <- constrA_assoc, put_put. reflexivity.
    rewrite constrA_spec. cbn.
      unfold bind_ContT, pure_ContT, ap_ContT, fmap_ContT, const, id, compose.
      ext k. rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc.
      rewrite bind_pure_l. reflexivity.
    cbn. unfold bind_ContT, pure_ContT.
      ext k. rewrite bind_constrA_comm, get_put, constrA_pure_l. reflexivity.
    cbn. unfold bind_ContT.
      ext k'. rewrite get_get. reflexivity.
Defined.

(*
TODO Instance MonadFree_ContT
  (R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFree S M inst)
  : MonadFree S (ContT R M) (Monad_ContT R M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  intros. ext k. cbn. unfold fmap_ContT, const, id.
    rewrite <- constrA_assoc. rewrite put_put. reflexivity.
  Focus 3.
  intros A f. ext k. cbn. unfold bind_ContT, pure_ContT.
    rewrite get_get. reflexivity.
*)