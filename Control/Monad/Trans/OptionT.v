Require Import Control.

Require Import HSLib.Control.Monad.All.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Definition fmap_OptionT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : OptionT M A -> OptionT M B :=
    fmap (fmap_Option f).

Hint Unfold OptionT fmap_OptionT : HSLib.

Instance Functor_OptionT (M : Type -> Type) {inst : Functor M}
    : Functor (OptionT M) :=
{
    fmap := fmap_OptionT
}.
Proof. all: hs; mtrans; monad. Defined.

Definition pure_OptionT
  {M : Type -> Type} {inst : Monad M} {A : Type} (x : A) : OptionT M A :=
    pure $ Some x.

Definition ap_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mof : OptionT M (A -> B)) (moa : OptionT M A) : OptionT M B :=
    @bind M inst _ _ mof (fun of =>
    match of with
        | Some f =>
            @bind M inst _ _ moa (fun oa =>
            match oa with
                | Some a => pure (Some (f a))
                | None => pure None
            end)
        | _ => pure None
    end).

Hint Unfold pure_OptionT ap_OptionT : HSLib.

Instance Applicative_OptionT
  (M : Type -> Type) (inst : Monad M) : Applicative (OptionT M) :=
{
    is_functor := @Functor_OptionT M inst;
    pure := @pure_OptionT M inst;
    ap := @ap_OptionT M inst;
}.
Proof. Time all: monad. Defined.

Definition aempty_OptionT
  (M : Type -> Type) (inst : Monad M) (A : Type) : OptionT M A :=
    pure None.

Definition aplus_OptionT
  (M : Type -> Type) (inst : Monad M) (A : Type) (mox moy : OptionT M A)
    : OptionT M A :=
    @bind M inst _ _ mox (fun ox =>
    @bind M inst _ _ moy (fun oy =>
    match ox, oy with
        | Some x, _ => pure (Some x)
        | _, Some y => pure (Some y)
        | _, _ => pure None
    end)).

Hint Unfold aempty_OptionT aplus_OptionT : HSLib.

Instance Alternative_OptionT
  (M : Type -> Type) (inst : Monad M) : Alternative (OptionT M) :=
{
    is_applicative := Applicative_OptionT M inst;
    aempty := aempty_OptionT M inst;
    aplus := aplus_OptionT M inst;
}.
Proof. Time all: monad. Defined.

Definition bind_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (moa : OptionT M A) (f : A -> OptionT M B) : OptionT M B :=
    @bind M inst (option A) (option B) moa (fun oa : option A =>
    match oa with
        | None => pure None
        | Some a => f a
    end).

Hint Unfold bind_OptionT : HSLib.

Instance Monad_OptionT
  (M : Type -> Type) (inst : Monad M) : Monad (OptionT M) :=
{
    is_applicative := Applicative_OptionT M inst;
    bind := @bind_OptionT M inst
}.
Proof. all: monad. Defined.

Instance MonadPlus_OptionT
  (M : Type -> Type) (inst : Monad M) : MonadPlus (OptionT M) :=
{
    is_monad := Monad_OptionT M inst;
    is_alternative := Alternative_OptionT M inst;
}.

Definition lift_OptionT {M : Type -> Type} {_inst : Monad M} {A : Type}
  (ma : M A) : OptionT M A := fmap Some ma.

Hint Unfold lift_OptionT : HSLib.

Instance MonadTrans_OptionT : MonadTrans OptionT :=
{
    is_monad := @Monad_OptionT;
    lift := @lift_OptionT;
}.
Proof. all: monad. Defined.

Require Import Control.Monad.Class.All.

Definition fail_OptionT
  {M : Type -> Type} {inst : Monad M} {A : Type}
    : OptionT M A := pure None.

Instance MonadFail_Option
  (M : Type -> Type) (inst : Monad M)
  : MonadFail (OptionT M) (Monad_OptionT M inst) :=
{
    fail := @fail_OptionT M inst
}.
Proof.
  intros. unfold fail_OptionT. cbn. unfold bind_OptionT.
  rewrite bind_pure_l. reflexivity.
Defined.

Require Import Control.Monad.Class.All.

Instance MonadAlt_OptionT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (OptionT M) (Monad_OptionT M inst) :=
{
    choose :=
      fun (A : Type) (mx my : M (option A)) => do
        x <- mx;
        y <- my;
        match x, y with
                | Some a, Some b => fmap Some $ choose (pure a) (pure b)
                | Some a, _ => pure (Some a)
                | _, Some a => pure (Some a)
                | _, _ => pure None
        end
}.
Proof.
  intros.
    rewrite !bind_assoc. f_equal. ext ox.
    rewrite !bind_assoc. f_equal. ext oy.
    rewrite !bind_assoc. destruct ox, oy; cbn.
      rewrite choose_bind_l.
  monad. 
  intros. unfold OptionT in *.
    Check (@bind_assoc M inst _ _ _ x).
    Check x >>= f.
    rewrite <- bind_assoc. f_equal. ext ox.
    rewrite !bind_assoc. f_equal. ext oy.
    rewrite !bind_assoc. destruct ox, oy; cbn. all: monad.
    
 Check
      fun ox oy => ox >>= fun x => oy >>= fun y =>
        match x, y with
            | Some a, _ => pure (Some a)
            | _, Some a => pure (Some a)
            | _, _ => pure None
        end.
    intros.
{
    choose :=
      fun A x y => (do
        x' <- x;
        y' <- y;
        pure (choose x' y'));
}.
Proof.
  intros. ext k. rewrite choose_assoc. reflexivity.
  intros. ext k. cbn. reflexivity.
Defined.

Instance MonadFail_OptionT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (OptionT M) (Monad_OptionT M) :=
{
    fail := fun A k => fail >>= k
}.
Proof.
  intros. cbn. monad. rewrite !bind_fail_l. reflexivity.
Defined.

Instance MonadNondet_OptionT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (OptionT M) (Monad_OptionT M) :=
{
    instF := @MonadFail_OptionT M inst (@instF _ _ inst');
    instA := @MonadAlt_OptionT M inst (@instA _ _ inst');
}.
Proof.
  intros. cbn. ext k. rewrite bind_fail_l, choose_fail_l. reflexivity.
  intros. cbn. ext k. rewrite bind_fail_l, choose_fail_r. reflexivity.
Defined.

Instance MonadReader_OptionT
  (E R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (OptionT M) (Monad_OptionT M) :=
{
    ask := fun k => ask >>= k
}.
Proof.
  ext k. cbn. unfold fmap_OptionT. unfold const, id.
Abort.

Instance MonadState_OptionT
  (S R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (OptionT M) (Monad_OptionT M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  intros. ext k. cbn. unfold fmap_OptionT, const, id.
    rewrite <- constrA_assoc. rewrite put_put. reflexivity.
  Focus 3.
  intros A f. ext k. cbn. unfold bind_OptionT, pure_OptionT.
    rewrite get_get. reflexivity.
Abort.

(*
Instance MonadFree_OptionT
  (R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadFree S M inst)
  : MonadFree S (OptionT M) (Monad_OptionT M) :=
{
    get := fun k => get >>= k;
    put := fun s k => put s >> k tt;
}.
Proof.
  intros. ext k. cbn. unfold fmap_OptionT, const, id.
    rewrite <- constrA_assoc. rewrite put_put. reflexivity.
  Focus 3.
  intros A f. ext k. cbn. unfold bind_OptionT, pure_OptionT.
    rewrite get_get. reflexivity.
Abort.
*)