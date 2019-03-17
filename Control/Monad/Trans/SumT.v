Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.
Require Import Control.Monad.Identity.

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
Proof. Time all: monad. Defined.

Theorem SumT_not_Alternative :
  (forall (E : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (SumT E M)) -> False.
Proof.
  intros. destruct (X False Identity Monad_Identity).
  clear -aempty. specialize (aempty False).
  compute in aempty. destruct aempty; assumption.
Qed.

Definition aempty_SumT
  (E : Type) {M : Type -> Type} {instA : Alternative M}
  {A : Type} : SumT E M A := fmap inr aempty.

Definition aplus_SumT
  {E : Type} {M : Type -> Type} {instA : Alternative M}
  {A : Type} (x y : SumT E M A) : SumT E M A :=
    @aplus _ instA _ x y.

Hint Unfold aempty_SumT aplus_SumT : HSLib.

Instance Alternative_SumT
  (E : Type) (M : Type -> Type) (instM : Monad M) (instA : Alternative M)
  : Alternative (SumT E M) :=
{
    is_applicative := Applicative_SumT E M instM;
    aempty := @aempty_SumT E M instA;
    aplus := @aplus_SumT E M instA;
}.
Proof. all: monad. Abort.

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

Definition lift_SumT
  (E : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
  : SumT E M A := fmap inr ma.

Hint Unfold lift_SumT : HSLib.

Instance MonadTrans_SumT (E : Type) : MonadTrans (SumT E) :=
{
    is_monad := @Monad_SumT E;
    lift := @lift_SumT E;
}.
Proof. all: monad. Defined.

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
Proof.
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

Instance MonadAlt_SumT
  (E : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (SumT E M) (Monad_SumT E M inst) :=
{
    choose :=
      fun A x y => @choose M inst inst' _ x y
}.
Proof.
  intros. rewrite choose_assoc. reflexivity.
  intros. cbn. unfold bind_SumT. rewrite bind_choose_l. reflexivity.
Defined.

Instance MonadAlt_SumT'
  (E : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (SumT E M) (Monad_SumT E M inst).
esplit. Unshelve.
  Focus 3. unfold SumT. intros A x y.
  apply (@bind M inst _ _ x).
  destruct 1.
    exact y.
    apply (@bind M inst _ _ y).
      destruct 1.
        exact (pure (inr a)).
        exact (choose (pure (inr a)) (pure (inr a0))).
Proof.
  intros. cbn. rewrite !bind_assoc. f_equal. ext ex. destruct ex; cbn.
    reflexivity.
    rewrite !bind_assoc. f_equal. ext ex. destruct ex; cbn.
      rewrite bind_pure_l. reflexivity.
      rewrite bind_choose_l, !bind_pure_l, bind_assoc.
Abort.

Instance MonadNondet_SumT
  (E : Type) (e : E) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (SumT E M) (Monad_SumT E M inst) :=
{
    instF := @MonadFail_SumT E M inst e;
    instA := @MonadAlt_SumT E M inst (@instA _ _ inst');
}.
Proof.
  intros. cbn. unfold fail_SumT. admit.
  intros. cbn. unfold fail_SumT. admit.
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

Instance MonadWriter_SumT
  (W : Monoid) (E : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadWriter W M inst)
  : MonadWriter W (SumT E M) (Monad_SumT E M inst) :=
{
    tell w := fmap inr (tell w);
    listen :=
      fun A (m : M (E + A)%type) =>
      listen m >>=
        fun '(ea, w) => pure
        match ea with
            | inl e => inl e
            | inr a => inr (a, w)
        end
}.
Proof.
  intros. cbn. unfold pure_SumT.
    rewrite listen_pure, bind_pure_l. reflexivity.
  intros. cbn. unfold fmap_SumT.
(*
  replace (fun '(ea, w) => pure _)
     with ((fun eaw : (E + A)%type * W =>
            match fst eaw with
                | inl e => inl e
                | inr a => inr (a, snd eaw)
            end) .> pure).

 rewrite fmap_bind_pure.
    rewrite bind_assoc.
    rewrite (bind_fmap M inst (E + A * W) (E + A * W * W) _
      (fun a : E + A * W =>
        match a with
        | inl e => inl e
        | inr a0 => inr (let '(a1, w) := a0 in (a1, w, neutr))
        end)
        _ pure).

 replace (fun a => pure _) with ((fun a => _) .> pure).

 Search bind fmap.

 rewrite <- fmap_bind_pure.*)
Abort.

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
      rewrite !bind_assoc. rewrite !bind_pure_l.
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
            fun sa : E + S =>
            match sa with
                | inl e => pure (inl e)
                | inr a => k a a
            end)
      with
        (fun s : S => k s s).
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

Instance MonadFree_SumT
  (F : Type -> Type) (instF : Functor F)
  (E : Type) (M : Type -> Type)
  (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (SumT E M) instF (Monad_SumT E M instM) :=
{
    wrap := fun A m => @wrap F M instF instM instMF _ m
}.
Proof.
  intros. cbn. unfold bind_SumT, pure_SumT,SumT in *.
  rewrite wrap_law.
  rewrite (wrap_law _ _ (fun a : A => pure (inr a)) x).
  monad.
Defined.