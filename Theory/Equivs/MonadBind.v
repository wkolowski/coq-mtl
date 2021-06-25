Require Import Control.Applicative.

(** This is a minimal [bind]-based definition of a monad. It says that a
    monad is something that can turn a value into a computation ([pure])
    and feed a computation into a function which expects a value and
    returns a computation ([bind]). These two are related by the three
    usual laws. *)
Class Monad (M : Type -> Type) : Type :=
{
    pure : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    bind_pure_l :
      forall (A B : Type) (f : A -> M B) (a : A),
        bind (pure a) f = f a;
    bind_pure_r :
      forall (A : Type) (ma : M A),
        bind ma pure = ma;
    bind_assoc :
      forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
        bind (bind ma f) g = bind ma (fun x => bind (f x) g);
}.

Notation "mx >>= f" := (bind mx f) (at level 40).

Hint Rewrite @bind_pure_l @bind_pure_r @bind_assoc : MonadBind.

(** A simple tactic for proving things about this definition. *)
Ltac mbind :=
  repeat (
    cbn; intros;
    autounfold with MonadBind;
    autorewrite with MonadBind;
    f_equal; exts; try reflexivity).

(** We can map [f] over a computation by binding it to [f] followed by
    [pure]. *)
Definition fmap_MonadBind
  {M : Type -> Type} {inst : Monad M}
  {A B : Type} (f : A -> B) (ma : M A) : M B :=
    ma >>= (f .> pure).

Global Hint Unfold fmap_MonadBind compose : MonadBind.

#[refine]
Instance Functor_MonadBind
  (M : Type -> Type) (inst : Monad M) : Functor M :=
{
    fmap := @fmap_MonadBind M inst;
}.
Proof. all: mbind. Defined.

(** We can perform [ap] by running both computations, applying the function
    to the argument and then turning this into a computation with [pure]. *)
Definition ap_MonadBind
  (M : Type -> Type) (inst : Monad M)
  (A B : Type) (mf : M (A -> B)) (ma : M A) : M B :=
    mf >>= fun f => ma >>= fun a => pure (f a).

Global Hint Unfold ap_MonadBind : MonadBind.

#[refine]
Instance Applicative_MonadBind
  (M : Type -> Type) (inst : Monad M) : Applicative M :=
{
    pure := @pure M inst;
    ap := @ap_MonadBind M inst;
}.
Proof. all: mbind. Defined.