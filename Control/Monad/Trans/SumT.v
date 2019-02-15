Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition SumT (E : Type) (M : Type -> Type) (A : Type)
  : Type := M (sum E A).

Definition fmap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type} (f : A -> B)
  : SumT E M A -> SumT E M B :=
    fmap (fun sa : sum E A =>
    match sa with
        | inl e => inl e
        | inr a => inr (f a)
    end).

Hint Unfold SumT fmap_SumT : HSLib.

Instance Functor_SumT
  {M : Type -> Type} {inst : Monad M} {E : Type} : Functor (SumT E M) :=
{
    fmap := @fmap_SumT M inst E
}.
Proof. all: hs; mtrans; monad. Defined.

Definition pure_SumT
  {M : Type -> Type} {inst : Monad M} {E A : Type} (x : A)
  : SumT E M A := pure (inr x).

Definition ap_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (msf : SumT E M (A -> B)) (msx : SumT E M A) : SumT E M B :=
    @bind M inst _ _ msf (fun sf =>
      match sf with
          | inl e => pure (inl e)
          | inr f =>
              @bind M inst _ _ msx (fun sx =>
              match sx with
                  | inl e => pure (inl e)
                  | inr x => pure (inr (f x))
              end)
      end).

Hint Unfold pure_SumT ap_SumT : HSLib.

Instance Applicative_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Applicative (SumT E M) :=
{
    is_functor := @Functor_SumT M inst E;
    pure := @pure_SumT M inst E;
    ap := @ap_SumT M inst E;
}.
Proof. all: hs; monad. Defined.

Theorem SumT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (SumT E M)) -> False.
Proof.
  intros. destruct (X False Identity MonadIdentity).
  clear -aempty. specialize (aempty False).
  compute in aempty. destruct aempty; assumption.
Qed.

Definition aempty_SumT
  (E : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : SumT E M A := fmap inr aempty.

Definition aplus_SumT
  {E : Type} {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (x y : SumT E M A) : SumT E M A :=
    @aplus _ instA _ x y.

Hint Unfold aempty_SumT aplus_SumT : HSLib.

Instance Alternative_SumT
  (E : Type) (M : Type -> Type) (inst : MonadPlus M)
  : Alternative (SumT E M) :=
{
    is_applicative := Applicative_SumT E M inst;
    aempty := @aempty_SumT E M inst inst;
    aplus := @aplus_SumT E M inst inst;
}.
Proof. all: hs. Defined.

Definition bind_SumT
  {M : Type -> Type} {inst : Monad M} {E A B : Type}
  (ma : SumT E M A) (f : A -> SumT E M B) : SumT E M B :=
    @bind M inst _ _ ma (fun sa : E + A =>
    match sa with
        | inl e => pure (inl e)
        | inr a => f a
    end).

Hint Unfold bind_SumT : HSLib.

Instance Monad_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) : Monad (SumT E M) :=
{
    is_applicative := @Applicative_SumT E M inst;
    bind := @bind_SumT M inst E;
}.
Proof. all: hs; monad. Defined.

Theorem SumT_not_MonadPlus :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (SumT E M)) -> False.
Proof.
  intros. apply SumT_not_Alternative.
  intros. destruct (X E M inst). assumption.
Qed.

Instance MonadPlus_SumT
  (E : Type) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (SumT E M) :=
{
    is_monad := @Monad_SumT E M inst;
    is_alternative := @Alternative_SumT E M inst;
}.
Proof. hs. Defined.

Definition lift_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
  : SumT E M A := fmap inr ma.

Hint Unfold lift_SumT : HSLib.

Instance MonadTrans_SumT (E : Type) : MonadTrans (SumT E) :=
{
    is_monad := @Monad_SumT E;
    lift := @lift_SumT E;
}.
Proof. all: hs; monad. Defined.

Require Import Control.Monad.Class.All.

Definition fail_SumT
  {E : Type} {M : Type -> Type} {inst : Monad M} (e : E) {A : Type}
    : SumT E M A := pure $ inl e.

Instance MonadFail_SumT
  (E : Type) (M : Type -> Type) {inst : Monad M} (e : E)
  : MonadFail (SumT E M) (Monad_SumT E M inst) :=
{
    fail := @fail_SumT E M inst e
}.
Proof. intros. unfold fail_SumT. monad. Defined.

Instance MonadExcept_SumT
  (E : Type) (e : E) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (SumT E M) (Monad_SumT E M inst) :=
{
    instF := @MonadFail_SumT E M inst e;
    catch :=
      fun A x y =>
      @bind M inst _ _ x (fun ea =>
      match ea with
          | inl e => y (*pure (inl e)*)
          | inr a => pure (inr a)
      end)
}.
Proof. Print MonadExcept.
  all: cbn; intros.
    unfold fail_SumT. rewrite bind_pure_l. reflexivity.
    Focus 2. rewrite bind_assoc. f_equal. ext ea. destruct ea.
      reflexivity.
      rewrite bind_pure_l. reflexivity.
    Focus 2. unfold pure_SumT. rewrite bind_pure_l. reflexivity.
    rewrite <- (@bind_pure_r M inst _ x) at 2. f_equal.
      ext ea. destruct ea. unfold fail_SumT.
    rewrite <- bind_pure_r. cbn. unfold bind_SumT.
      f_equal.
Abort.

(* BIG TODO *)

Instance MonadAlt_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (SumT E M) (Monad_SumT E M inst) :=
{
    choose :=
      fun A x y => @choose M inst inst' _ x y
}.
Proof.
  intros. rewrite choose_assoc. reflexivity.
  intros. cbn. unfold bind_SumT. rewrite choose_bind_l. reflexivity.
Defined.

Instance MonadNondet_SumT
  (E : Type) (e : E) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (SumT E M) (Monad_SumT E M inst) :=
{
    instF := @MonadFail_SumT E M inst e;
    instA := @MonadAlt_SumT E M inst (@instA _ _ inst');
}.
Proof.
  intros. cbn. unfold fail_SumT. Print MonadAlt. admit.
  intros. cbn. unfold fail_SumT. Print MonadNondet. admit.
Admitted.

Instance MonadReader_SumT
  (E R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader R M inst)
  : MonadReader R (SumT E M) (Monad_SumT E M inst) :=
{
    ask := ask >>= fun x => pure (inr x)
}.
Proof.
  rewrite <- ask_ask at 3. rewrite !constrA_spec. monad.
Defined.

Instance MonadState_SumT
  (E S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (SumT E M) (Monad_SumT E M inst) :=
{
    get := get >>= fun x => pure (inr x);
    put := fun s => put s >> pure (inr tt);
}.
Proof.
  all: intros.
    monad.
    rewrite !constrA_spec. cbn. unfold bind_SumT, pure_SumT.
      rewrite !bind_assoc. wut. wut.
      rewrite <- constrA_spec, constrA_bind_assoc, put_get.
      rewrite <- constrA_bind_assoc, bind_pure_l, <- constrA_spec.
      reflexivity.
    cbn. unfold bind_SumT, pure_SumT.
      rewrite bind_assoc, <- fmap_pure at 1.
      rewrite <- get_put, fmap_bind. f_equal. monad.
    cbn. unfold bind_SumT. rewrite !bind_assoc.
      replace
        (fun x : S =>
 pure (inr x) >>=
 (fun sa : E + S =>
  match sa with
  | inl e => pure (inl e)
  | inr a => k a a
  end))
         with (fun s : S => k s s).
        rewrite <- get_get. f_equal. monad.
        ext s. rewrite bind_pure_l. reflexivity.
Defined.

Instance MonadStateNondet_SumT
  (E S : Type) (e : E) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (SumT E M) (Monad_SumT E M inst) :=
{
    instS := MonadState_SumT E S M inst inst';
    instN := MonadNondet_SumT E e M inst inst';
}.
Proof.
Abort.

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