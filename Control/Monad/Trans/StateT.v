Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.
Require Import Control.Monad.Identity.

(** A transformer which adds a layer of the state monad on top of any
    monad [M]. *)
Definition StateT (S : Type) (M : Type -> Type) (A : Type)
  : Type := S -> M (A * S)%type.

Definition fmap_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> B)
  : StateT S M A -> StateT S M B :=
    fun (x : StateT S M A) (s : S) =>
      x s >>= fun '(a, s') => pure (f a, s').

Hint Unfold StateT fmap_StateT compose : HSLib.

(** These lemmas are there so that the parsers are fast. I don't know why
    that matters, but it does... *)

Lemma f1 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A : Type),
    fmap_StateT S (@id A) = id.
Proof. monad. Qed.

Lemma f2 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (f : A -> B) (g : B -> C),
    fmap_StateT S (f .> g) = fmap_StateT S f .> fmap_StateT S g.
Proof. monad. Qed.

Instance Functor_StateT
  {S : Type} {M : Type -> Type} {inst : Monad M} : Functor (StateT S M) :=
{
    fmap := @fmap_StateT S M inst
}.
Proof.
  apply f1.
  apply f2.
Defined.

Definition pure_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : StateT S M A := fun s => pure (x, s).

Definition ap_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (sf : StateT S M (A -> B)) (sa : StateT S M A) : StateT S M B :=
    fun st : S =>
      sf st >>= fun '(f, stf) =>
      sa stf >>= fun '(a, sta) =>
        pure (f a, sta).

Hint Unfold pure_StateT ap_StateT : HSLib.

Lemma p1 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A : Type)
  (x : StateT S M A),
    ap_StateT S (pure_StateT S id) x = x.
Proof. monad. Qed.

Lemma p2 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (af : StateT S M (A -> B)) (ag : StateT S M (B -> C)) (ax : StateT S M A),
    ap_StateT S (ap_StateT S (ap_StateT S (pure_StateT S compose) ag) af) ax =
    ap_StateT S ag (ap_StateT S af ax).
Proof. monad. Qed.

Lemma p3 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> B) (x : A),
    ap_StateT S (pure_StateT S f) (pure_StateT S x) = pure_StateT S (f x).
Proof. monad. Qed.

Lemma p4 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : StateT S M (A -> B)) (x : A),
    ap_StateT S f (pure_StateT S x) =
    ap_StateT S (pure_StateT S (fun f0 : A -> B => f0 x)) f.
Proof. monad. Qed.

Lemma p5 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> B) (x : StateT S M A),
    fmap f x = ap_StateT S (pure_StateT S f) x.
Proof. monad. Qed.

Instance Applicative_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) : Applicative (StateT S M) :=
{
    is_functor := @Functor_StateT S M inst;
    pure := @pure_StateT S M inst;
    ap := @ap_StateT S M inst;
}.
Proof.
  apply p1.
  apply p2.
  apply p3.
  apply p4.
  apply p5.
Defined.

Theorem StateT_not_Alternative :
  (forall (S : Type) (M : Type -> Type) (inst : Monad M),
    Alternative (StateT S M)) -> False.
Proof.
  intros. destruct (X unit Identity Monad_Identity).
  clear -aempty. specialize (aempty False).
  compute in aempty. apply aempty. exact tt.
Qed.

Definition aempty_StateT
  (S : Type) {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} : StateT S M A :=  fun s : S => aempty.

Definition aplus_StateT
  {S : Type} {M : Type -> Type} {instM : Monad M} {instA : Alternative M}
  {A : Type} (x y : StateT S M A) : StateT S M A :=
    fun s : S => x s <|> y s.

Hint Unfold aempty_StateT aplus_StateT : HSLib.

Instance Alternative_StateT
  (S : Type) (M : Type -> Type) (instM : Monad M) (instA : Alternative M)
  : Alternative (StateT S M) :=
{
    is_applicative := Applicative_StateT S M instM;
    aempty := @aempty_StateT S M instM instA;
    aplus := @aplus_StateT S M instM instA;
}.
Proof. all: monad. Defined.

Definition bind_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
    fun s : S => x s >>= (fun '(a, s') => f a s').

Hint Unfold bind_StateT : HSLib.

Lemma m1 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> StateT S M B) (a : A),
    bind_StateT S (pure a) f = f a.
Proof. monad. Qed.

Lemma m2 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A : Type)
  (ma : StateT S M A),
    bind_StateT S ma pure = ma.
Proof. monad. Qed.

Lemma m3 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (ma : StateT S M A) (f : A -> StateT S M B) (g : B -> StateT S M C),
    bind_StateT S (bind_StateT S ma f) g =
    bind_StateT S ma (fun x : A => bind_StateT S (f x) g).
Proof. monad. Qed.

Lemma m4 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> B) (x : StateT S M A),
    fmap f x = bind_StateT S x (fun a : A => pure (f a)).
Proof. monad. Qed.

Lemma m5 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mf : StateT S M (A -> B)) (mx : StateT S M A),
    mf <*> mx =
      bind_StateT S mf (fun f : A -> B =>
      bind_StateT S mx (fun x : A => pure (f x))).
Proof. monad. Qed.

Instance Monad_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) : Monad (StateT S M) :=
{
    is_applicative := @Applicative_StateT S M inst;
    bind := @bind_StateT S M inst;
}.
Proof.
  apply m1.
  apply m2.
  apply m3.
  apply m5.
(*
Restart.
  all: monad.*)
Defined.

Definition lift_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : StateT S M A := fun s : S => ma >>= fun a : A => pure (a, s).

Hint Unfold lift_StateT : HSLib.

Instance MonadTrans_StateT (S : Type) : MonadTrans (StateT S) :=
{
    is_monad := @Monad_StateT S;
    lift := @lift_StateT S;
}.
Proof. all: monad. Defined.

Instance MonadState_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadState S (StateT S M) (Monad_StateT S M inst) :=
{
    get := fun s : S => pure (s, s);
    put := fun s : S => fun _ => pure (tt, s)
}.
Proof.
  1-3: monad.
  intros. ext s. hs.
Defined.

Instance MonadAlt_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadAlt M inst)
  : MonadAlt (StateT S M) (Monad_StateT S M inst) :=
{
    choose :=
      fun A x y s => choose (x s) (y s)
}.
Proof. all: monad. Defined.

Instance MonadFail_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadFail M inst)
  : MonadFail (StateT S M) (Monad_StateT S M inst) :=
{
    fail := fun A s => fail
}.
Proof. monad. Defined.

Instance MonadNondet_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) (inst' : MonadNondet M inst)
  : MonadNondet (StateT S M) (Monad_StateT S M inst) :=
{
    instF := @MonadFail_StateT S M inst (@instF _ _ inst');
    instA := @MonadAlt_StateT S M inst (@instA _ _ inst');
}.
Proof. all: monad. Defined.

Instance MonadExcept_StateT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (StateT S M) (Monad_StateT S M inst) :=
{
    instF := @MonadFail_StateT S M inst inst';
    catch :=
      fun A x y => fun s => catch (x s) (y s);
}.
Proof. all: monad. Defined.

Instance MonadReader_StateT
  (E S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (StateT S M) (Monad_StateT S M inst) :=
{
    ask := fun s => ask >>= fun e => pure (e, s);
}.
Proof.
  rewrite constrA_spec. cbn. unfold bind_StateT.
  ext s. rewrite bind_assoc.
  rewrite <- ask_ask at 2.
  rewrite constrA_spec. monad.
Defined.

Instance MonadWriter_StateT
  (W : Monoid) (S : Type) (M : Type -> Type) (inst : Monad M)
  : MonadWriter W (StateT S M) (Monad_StateT S M inst) :=
{
    tell := fun w => fun s => pure (tt, s);
    listen :=
      fun A (m : S -> M (A * S)%type) =>
        fun s =>
          m s >>= fun '(a, s) => pure (a, neutr, s);
}.
Proof. all: monad. Defined.

Instance MonadStateNondet_StateT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadStateNondet S M inst)
  : MonadStateNondet S (StateT S M) (Monad_StateT S M inst) :=
{
    instS := MonadState_StateT S M inst;
    instN := MonadNondet_StateT S M inst inst';
}.
Proof.
  intros. rewrite constrA_spec. cbn. unfold bind_StateT.
    ext s. rewrite <- (seq_fail_r _ _ (x s)) at 1.
    rewrite constrA_spec. f_equal. ext y. destruct y. reflexivity.
  intros. cbn. unfold bind_StateT.
    ext s. rewrite <- bind_choose_r. f_equal. ext x. destruct x.
    reflexivity.
Defined.

Instance MonadFree_StateT
  (F : Type -> Type) (instF : Functor F)
  (S : Type) (M : Type -> Type)
  (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (StateT S M) instF (Monad_StateT S M instM) :=
{
    wrap :=
      fun A m s => wrap (fmap (fun x => x s) m)
}.
Proof.
  intros. ext s. cbn.
  unfold bind_StateT, pure_StateT, StateT in *.
  rewrite <- !fmap_comp'. unfold compose.
  rewrite wrap_law.
  rewrite (wrap_law _ _ (fun a : A => pure (a, s)) x).
  rewrite bind_assoc. f_equal. ext a.
  rewrite bind_pure_l. reflexivity.
Defined.