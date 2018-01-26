Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Control.MonadPlus.
Require Export Control.MonadTrans.

Require Import HSLib.Instances.Identity.


Definition StateT (S : Type) (M : Type -> Type) (A : Type)
  : Type := S -> M (A * S)%type.

Definition fmap_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> B)
  : StateT S M A -> StateT S M B :=
    fun (x : StateT S M A) (s : S) =>
      x s >>= fun '(a, s') => ret (f a, s').

Hint Unfold StateT fmap_StateT compose (* BEWAR *): HSLib.

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
(*
Proof.
  all: intros; unfold fmap_StateT; ext x; ext s.
    replace (x s >>= _ = _) with (x s >>= ret = id x s).
      monad.
      do 2 f_equal. ext p. destruct p. reflexivity.
    unfold compose. rewrite assoc. f_equal. ext p. destruct p.
      monad.
Defined.
*)
Definition ret_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : StateT S M A := fun s => ret (x, s).

Definition ap_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (sf : StateT S M (A -> B)) (sa : StateT S M A) : StateT S M B :=
    fun st : S =>
      sf st >>= fun '(f, stf) =>
      sa stf >>= fun '(a, sta) =>
        ret (f a, sta).

Hint Unfold ret_StateT ap_StateT : HSLib.

Lemma p1 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A : Type)
  (x : StateT S M A),
    ap_StateT S (ret_StateT S id) x = x.
Proof. monad. Qed.

Lemma p2 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (af : StateT S M (A -> B)) (ag : StateT S M (B -> C)) (ax : StateT S M A),
    ap_StateT S (ap_StateT S (ap_StateT S (ret_StateT S compose) ag) af) ax =
    ap_StateT S ag (ap_StateT S af ax).
Proof. monad. Qed.

Lemma p3 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> B) (x : A),
    ap_StateT S (ret_StateT S f) (ret_StateT S x) = ret_StateT S (f x).
Proof. monad. Qed.

Lemma p4 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : StateT S M (A -> B)) (x : A),
    ap_StateT S f (ret_StateT S x) =
    ap_StateT S (ret_StateT S (fun f0 : A -> B => f0 x)) f.
Proof. monad. Qed.

Lemma p5 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> B) (x : StateT S M A),
    fmap f x = ap_StateT S (ret_StateT S f) x.
Proof. monad. Qed.

Instance Applicative_StateT
  (S : Type) (M : Type -> Type) (inst : Monad M) : Applicative (StateT S M) :=
{
    is_functor := @Functor_StateT S M inst;
    ret := @ret_StateT S M inst;
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
  intros. destruct (X unit Identity MonadIdentity).
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
Proof.
  all: monad.
Defined.

Definition bind_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A B : Type}
  (x : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
    fun s : S => x s >>= (fun '(a, s') => f a s').

Hint Unfold bind_StateT : HSLib.

Lemma m1 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (f : A -> StateT S M B) (a : A),
    bind_StateT S (ret a) f = f a.
Proof. monad. Qed.

Lemma m2 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A : Type)
  (ma : StateT S M A),
    bind_StateT S ma ret = ma.
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
    fmap f x = bind_StateT S x (fun a : A => ret (f a)).
Proof. monad. Qed.

Lemma m5 :
  forall (S : Type) (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mf : StateT S M (A -> B)) (mx : StateT S M A),
    mf <*> mx =
      bind_StateT S mf (fun f : A -> B =>
      bind_StateT S mx (fun x : A => ret (f x))).
Proof. monad. Qed.

Instance Monad_StateT
  (S : Type) (M : Type -> Type) {inst : Monad M} : Monad (StateT S M) :=
{
    is_applicative := @Applicative_StateT S M inst;
    bind := @bind_StateT S M inst;
}.
Proof.
  apply m1.
  apply m2.
  apply m3.
  apply m4.
  apply m5.
Defined.

Theorem StateT_not_MonadPlus :
  (forall (S : Type) (M : Type -> Type) (inst : Monad M),
    MonadPlus (StateT S M)) -> False.
Proof.
  intros. apply StateT_not_Alternative.
  intros. destruct (X S M inst). assumption.
Qed.

Instance MonadPlus_StateT
  (S : Type) {M : Type -> Type} {inst : MonadPlus M}
  : MonadPlus (StateT S M) :=
{
    is_monad := @Monad_StateT S M inst;
    is_alternative := @Alternative_StateT S M inst inst;
}.
Proof. monad. Defined.

Definition lift_StateT
  (S : Type) {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : StateT S M A := fun s : S => ma >>= fun a : A => ret (a, s).

Hint Unfold lift_StateT : HSLib.

Instance MonadTrans_StateT (S : Type) : MonadTrans (StateT S) :=
{
    is_monad := @Monad_StateT S;
    lift := @lift_StateT S;
}.
Proof. all: monad. Defined.