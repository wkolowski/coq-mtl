Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition WriterT (W : Monoid) (M : Type -> Type) (A : Type)
  : Type := M (A * W)%type.

Definition fmap_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> B)
  (x : WriterT W M A) : WriterT W M B :=
    fmap (fun '(a, w) => (f a, w)) x.

Hint Unfold WriterT fmap_WriterT compose (* BEWARE *): HSLib.

Instance Functor_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} : Functor (WriterT W M) :=
{
    fmap := @fmap_WriterT W M inst
}.
Proof.
  all: monad.
Defined.

Definition pure_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : WriterT W M A := pure (x, neutr).

Definition ap_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mf : WriterT W M (A -> B)) (mx : WriterT W M A) : WriterT W M B :=
    @bind M inst _ _ mf (fun '(f, w) =>
    @bind M inst _ _ mx (fun '(x, w') =>
      pure (f x, op w w'))).

Hint Unfold pure_WriterT ap_WriterT : HSLib.

Instance Applicative_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M)
  : Applicative (WriterT W M) :=
{
    is_functor := @Functor_WriterT W M inst;
    pure := @pure_WriterT W M inst;
    ap := @ap_WriterT W M inst;
}.
Proof. all: monad. Defined.

Theorem WriterT_not_Alternative :
  (forall (W : Monoid) (M : Type -> Type) (inst : Monad M),
    Alternative (WriterT W M)) -> False.
Proof.
  intros. assert (W : Monoid).
    refine {| carr := unit; neutr := tt; op := fun _ _ => tt |}.
      1-3: try destruct x; reflexivity.
    destruct (X W Identity MonadIdentity).
    clear -aempty. specialize (aempty False).
    compute in aempty. destruct aempty. assumption.
Qed.

Definition aempty_WriterT
  (W : Monoid) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : WriterT W M A := fmap (fun a => (a, neutr)) aempty.

Definition aplus_WriterT
  {W : Monoid} {M : Type -> Type} {inst : MonadPlus M} {A : Type}
  (wx wy : WriterT W M A) : WriterT W M A :=
    @aplus M inst _ wx wy.

Hint Unfold aempty_WriterT aplus_WriterT : HSLib.

Instance Alternative_WriterT
  (W : Monoid) (M : Type -> Type) (inst : MonadPlus M)
  : Alternative (WriterT W M) :=
{
    is_applicative := Applicative_WriterT W M inst;
    aempty := @aempty_WriterT W M inst inst;
    aplus := @aplus_WriterT W M inst;
}.
Proof. all: monad. Defined.

Definition bind_WriterT
  {W : Monoid} {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : WriterT W M A) (f : A -> WriterT W M B) : WriterT W M B :=
    @bind M inst _ _ x (fun '(a, w) =>
    @bind M inst _ _ (f a) (fun '(b, w') =>
      pure (b, op w w'))).

Hint Unfold bind_WriterT : HSLib.

Instance Monad_WriterT
  (W : Monoid) (M : Type -> Type) {inst : Monad M} : Monad (WriterT W M) :=
{
    is_applicative := @Applicative_WriterT W M inst;
    bind := @bind_WriterT W M inst;
}.
Proof. all: monad. Defined.

Theorem WriterT_not_MonadPlus :
  (forall (W : Monoid) (M : Type -> Type) (inst : Monad M),
    MonadPlus (WriterT W M)) -> False.
Proof.
  intros. apply WriterT_not_Alternative.
  intros. destruct (X W M inst). assumption.
Qed.

Instance MonadPlus_WriterT
  (W : Monoid) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (WriterT W M) :=
{
    is_monad := @Monad_WriterT W M inst;
    is_alternative := @Alternative_WriterT W M inst;
}.
Proof. monad. Defined.

Definition lift_WriterT
  (W : Monoid) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : WriterT W M A := fmap (fun x : A => (x, neutr)) ma.

Hint Unfold lift_WriterT : HSLib.

Instance MonadTrans_WriterT (W : Monoid) : MonadTrans (WriterT W) :=
{
    is_monad := @Monad_WriterT W;
    lift := @lift_WriterT W;
}.
Proof. all: monad. Defined.

Require Import Control.Monad.Class.All.

Instance MonadAlt_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (WriterT W M) (Monad_WriterT W M) :=
{
    choose := fun A x y => @choose M inst inst' (A * W) x y
}.
Proof.
  intros.  cbn. rewrite choose_assoc. reflexivity.
  intros. cbn. unfold bind_WriterT. rewrite choose_bind_l. reflexivity.
Defined.

Instance MonadFail_WriterT
  (W : Monoid) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (WriterT W M) (Monad_WriterT W M) :=
{
    fail := fun A => @fail M inst inst' (A * W)
}.
Proof.
  intros. cbn. unfold bind_WriterT. rewrite bind_fail_l. reflexivity.
Defined.

Instance MonadNondet_WriterT
  (W : Monoid) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (WriterT W M) (Monad_WriterT W M) :=
{
    instF := @MonadFail_WriterT W M inst (@instF _ _ inst');
    instA := @MonadAlt_WriterT W M inst (@instA _ _ inst');
}.
Proof.
  intros. destruct inst'. apply choose_fail_l.
  intros. destruct inst'. apply choose_fail_r.
Defined.

Instance MonadExcept_WriterT
  (W : Monoid) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (WriterT W M) (Monad_WriterT W M) :=
{
    instF := @MonadFail_WriterT W M inst inst';
    catch := fun A x y => @catch M inst _ _ x y;
}.
Proof.
  all: cbn; intros.
    apply (@catch_fail_l _ _ _ (A * W)).
    apply (@catch_fail_r _ _ _ (A * W)).
    apply (@catch_assoc _ _ _ (A * W)).
    unfold pure_WriterT.
      apply (@catch_pure _ _ _ (A * W)).
Defined.

Instance MonadReader_WriterT
  (W : Monoid) (E : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (WriterT W M) (Monad_WriterT W M) :=
{
    ask := ask >>= fun e => pure (e, neutr)
}.
Proof.
  unfold constrA, const, id, compose.
  rewrite bind_ap, bind_fmap. unfold compose.
  rewrite <- bind_assoc. cbn. unfold bind_WriterT, pure_WriterT.
  rewrite !bind_assoc.
  replace
    (fun x : E =>
 @pure M inst (E * W) (x, @neutr W) >>=
 (fun x0 : E * W =>
  (let
   '(_, w) := x0 in
    (@ask E M inst inst' >>=
     (fun e : E => @pure M inst (E * W) (e, @neutr W))) >>=
    (fun '(b, w') => @pure M inst (E * W) (b, @op W w w'))) >>=
  (fun '(a, w) =>
   @pure M inst (E * W) (a, @neutr W) >>=
   (fun '(b, w') => @pure M inst (E * W) (b, @op W w w')))))
  with
    (fun e : E =>
      ((ask >>= (fun e0 : E => pure (e0, neutr))) >>=
 (fun '(b, w') => pure (b, op neutr w'))) >>=
(fun '(a, w) => pure (a, neutr) >>= (fun '(b, w') => pure (b, op w w')))
    ).
  2: {
    ext e. rewrite bind_pure_l. reflexivity.
  }
  rewrite <- constrA_spec.
  rewrite !bind_assoc, constrA_bind_assoc, ask_ask.
  f_equal.
  ext e. monad.
Defined.

Instance MonadState_WriterT
  (W : Monoid) (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (WriterT W M) (Monad_WriterT W M) :=
{
    get := get >>= fun s => pure (s, neutr);
    put := fun s => put s >> pure (tt, neutr);
}.
Proof.
  intros. cbn. unfold ap_WriterT, fmap_WriterT.
    rewrite bind_fmap. unfold compose, const, id.
    rewrite <- constrA_bind_assoc. rewrite bind_pure_l. monad.
    rewrite <- !constrA_spec, <- constrA_assoc, put_put.
    reflexivity.
  intro. cbn. unfold ap_WriterT, fmap_WriterT, pure_WriterT, const, id.
    rewrite !bind_fmap. unfold compose.
    rewrite <- !constrA_bind_assoc, !bind_pure_l.
    rewrite 2!constrA_bind_assoc. rewrite put_get.
    rewrite <- 2!constrA_bind_assoc. rewrite !bind_pure_l.
    reflexivity.
  cbn. unfold bind_WriterT, pure_WriterT.
    rewrite bind_assoc.
    replace

      (fun x : S =>
 @pure M inst (S * W) (x, @neutr W) >>=
 (fun '(a, w) =>
  (@put S M inst inst' a >> @pure M inst (unit * W) (tt, @neutr W)) >>=
  (fun '(b, w') => @pure M inst (unit * W) (b, @op W w w'))))

    with

      (fun s : S =>
        put s >> @pure M inst _ (tt, neutr))

    by monad.

    rewrite bind_constrA_comm, get_put, constrA_pure_l. reflexivity.
  intros. cbn. unfold bind_WriterT.
    rewrite bind_assoc.
Admitted. (* TODO *)

(*

TODO Instance MonadFree_WriterT
  (W : Monoid) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFree S M inst)
  : MonadFree S (WriterT W M) (Monad_WriterT W M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  intros. ext k. cbn. unfold fmap_WriterT, const, id.
    rewrite <- constrA_assoc. rewrite put_put. reflexivity.
  Focus 3.
  intros A f. ext k. cbn. unfold bind_WriterT, pure_WriterT.
    rewrite get_get. reflexivity.
*)