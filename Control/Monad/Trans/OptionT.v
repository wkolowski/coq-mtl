Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.
Require Import Control.Monad.Option.

(** A transformer that adds a layer of the partiality monad on top of
    any other monad. *)
Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

(** [fmap], [pure], [ap], [aempty], [aplus] and [bind] are defined just
    like for [option], but with [bind]s of the base monad inserted where
    necessary. *)

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
    pure (Some x).

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

(** We can lift a computation into the monad by wrapping it in the [Some]
    constructor. *)
Definition lift_OptionT
  {M : Type -> Type} {_inst : Monad M} {A : Type} (ma : M A)
    : OptionT M A := fmap Some ma.

Hint Unfold lift_OptionT : HSLib.

Instance MonadTrans_OptionT : MonadTrans OptionT :=
{
    is_monad := @Monad_OptionT;
    lift := @lift_OptionT;
}.
Proof. all: monad. Defined.

(** [OptionT] adds the ability to [fail] to any monad [M]. *)

Definition fail_OptionT
  {M : Type -> Type} {inst : Monad M} {A : Type}
    : OptionT M A := pure None.

Hint Unfold fail_OptionT : HSLib.

Instance MonadFail_OptionT
  (M : Type -> Type) (inst : Monad M)
  : MonadFail (OptionT M) (Monad_OptionT M inst) :=
{
    fail := @fail_OptionT M inst
}.
Proof. monad. Defined.

(** [OptionT] preserves [MonadAlt], giving us a monad with choice and
    failure, but the choice is very retarded: we perform it first, so
    that our chosen computation can later fail. This is also the reason
    why [OptionT] doesn't have [MonadNondet]. *)

Instance MonadAlt_OptionT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (OptionT M) (Monad_OptionT M inst) :=
{
    choose :=
      fun A x y => @choose M inst inst' _ x y
}.
Proof. all: monad. Defined.

Instance MonadNondet_OptionT
  (R : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (OptionT M) (Monad_OptionT M inst) :=
{
    instF := @MonadFail_OptionT M inst;
    instA := @MonadAlt_OptionT M inst (@instA _ _ inst');
}.
Proof.
  Focus 2. cbn. intros. unfold fail_OptionT.
Admitted.

(** Besides failing, [OptionT] adds to any monad the ability to catch the
    failure. *)
Instance MonadExcept_OptionT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (OptionT M) (Monad_OptionT M inst) :=
{
    instF := @MonadFail_OptionT M inst;
    catch :=
      fun A x y =>
        @bind M inst _ _ x (fun x' : option A =>
        match x' with
            | None => y
            | Some a => pure (Some a)
        end)
}.
Proof. all: monad. Defined.

(** [OptionT] preserves reading and state, but not writing. *)

Instance MonadReader_OptionT
  (E R : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (OptionT M) (Monad_OptionT M inst) :=
{
    ask := ask >>= fun e => pure (Some e)
}.
Proof.
  rewrite <- ask_ask at 3. rewrite <- constrA_bind_assoc. monad.
Defined.

Instance MonadWriter_OptionT
  (W : Monoid) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadWriter W M inst)
  : MonadWriter W (OptionT M) (Monad_OptionT M inst) :=
{
    tell w := fmap Some (tell w);
    listen := fun A x =>
      @listen W M inst inst' _ x >>= (fun '(oa, w) =>
      match oa with
          | None => pure None
          | Some a => pure (Some (a, w))
      end)
}.
Proof.
  intros. cbn. unfold pure_OptionT. rewrite listen_pure.
    rewrite bind_pure_l. reflexivity.
  Check @listen.
  
  intros. cbn. unfold pure_OptionT, fmap_OptionT, fmap_Option.
Abort.

Instance MonadState_OptionT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (OptionT M) (Monad_OptionT M inst) :=
{
    get := fmap Some get;
    put s := put s >> pure (Some tt);
}.
Proof.
  monad.
  hs. rewrite <- !bind_assoc. monad.
  cbn. unfold bind_OptionT, pure_OptionT. rewrite bind_fmap.
    unfold compose. rewrite bind_constrA_comm, get_put, constrA_pure_l.
    reflexivity.
  intros. cbn. unfold bind_OptionT.
    rewrite !bind_fmap. unfold compose.
    rewrite <- get_get. monad.
Defined.

(*
Instance MonadStateNondet_OptionT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (OptionT M) (Monad_OptionT M inst) :=
{
    instS := MonadState_OptionT S M inst inst';
    instN := MonadNondet_OptionT S M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn. compute.
    ext X. ext nil. ext cons. admit.
  intros. cbn. compute. ext X. ext nil. ext cons.
Abort.
*)

Instance MonadFree_OptionT
  (F : Type -> Type) (instF : Functor F)
  (M : Type -> Type) (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (OptionT M) instF (Monad_OptionT M instM) :=
{
    wrap := fun A m => @wrap F M instF instM instMF _ m
}.
Proof.
  hs.
  rewrite
    (wrap_law _ _ (fun x0 : A => @pure M instM (option A) (@Some A x0)) x).
  rewrite wrap_law, bind_assoc. monad.
Defined.