Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition OptionT (M : Type -> Type) (A : Type) : Type := M (option A).

Definition fmap_Option {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Definition fmap_OptionT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : OptionT M A -> OptionT M B :=
    fmap (fmap_Option f). (* (fun oa : option A =>
    match oa with
        | None => None
        | Some x => Some (f x)
    end).*)

Instance Functor_OptionT (M : Type -> Type) {inst : Functor M}
    : Functor (OptionT M) :=
{
    fmap := fmap_OptionT
}.
Proof.
  all: unfold fmap_OptionT, fmap_Option; functor.
Defined.

Definition ret_OptionT
  {M : Type -> Type} {inst : Monad M} {A : Type} (x : A) : OptionT M A :=
    ret $ Some x.

Definition ap_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mof : OptionT M (A -> B)) (moa : OptionT M A) : OptionT M B :=
    @bind M inst _ _ mof (fun of =>
    @bind M inst _ _ moa (fun oa =>
    match of, oa with
        | Some f, Some a => ret (Some (f a))
        | _, _ => ret None
    end)).

Instance Applicative_OptionT
  (M : Type -> Type) (inst : Monad M) : Applicative (OptionT M) :=
{
    is_functor := @Functor_OptionT M inst;
    ret := @ret_OptionT M inst;
    ap := @ap_OptionT M inst;
}.
Proof.
  Ltac wut := repeat (monad;
  match goal with
      | |- ?x >>= _ = ?x >>= _ => f_equal
      | |- context [match ?x with _ => _ end] => destruct x
      | |- ret = fun _ => _ => let x := fresh "x" in ext x
      | |- (fun _ => _) = (fun _ => _) => let x := fresh "x" in ext x
      | |- context [id] => unfold id
      | |- context [_ .> _] => unfold compose
      | M : Type -> Type, inst : Monad ?M |- context [_ >>= ?f] =>
          match f with
              | (fun _ : ?A => _) =>
                  match type of f with
                      | ?T -> _ => replace f with (@ret M inst T)
                  end
          end
      | _ => autorewrite with monad
  end; try congruence).
  all: cbn; unfold OptionT, fmap_OptionT, ret_OptionT, ap_OptionT; monad.
Defined.

Definition bind_OptionT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (moa : OptionT M A) (f : A -> OptionT M B) : OptionT M B :=
    @bind M inst (option A) (option B) moa (fun oa : option A =>
match oa with
    | None => ret None
    | Some a => f a
end).

Instance Monad_OptionT (M : Type -> Type) {inst : Monad M}
    : Monad (OptionT M) :=
{
    is_applicative := Applicative_OptionT M inst;
    bind := @bind_OptionT M inst
}.
Proof.
  all: cbn;
  unfold OptionT, fmap_OptionT, ret_OptionT, ap_OptionT, bind_OptionT; intros.
    rewrite bind_ret_l. reflexivity.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (option A))
    end.
      rewrite bind_ret_r. reflexivity.
      ext oa. destruct oa; reflexivity.
    rewrite assoc. f_equal. ext oa. destruct oa.
      reflexivity.
      rewrite bind_ret_l. reflexivity.
    rewrite bind_fmap. unfold compose. f_equal. ext oa.
      destruct oa; cbn; reflexivity.
    rewrite fmap_bind. f_equal. ext oa. destruct oa; cbn.
      reflexivity.
      rewrite fmap_ret. cbn. reflexivity.
    monad. Axiom huj : False. destruct huj. (* TODO *)
Defined.
(*Restart.
  From mathcomp Require Import ssreflect.
  all: intros; unfold bind_OptionT; cbn.
    by rewrite bind_ret_l.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (option A))
    end.
      by rewrite bind_ret_r.
      by ext oa; case: oa.
    rewrite assoc. f_equal. by ext oa; case: oa; rewrite ?bind_ret_l.
    by rewrite fmap_ret.
    rewrite bind_fmap /compose. f_equal. by ext oa; case: oa.
    rewrite fmap_bind. f_equal. by ext oa; case oa; rewrite ?fmap_ret.
Defined.*)

Definition lift_OptionT {M : Type -> Type} {_inst : Monad M} {A : Type}
  (ma : M A) : OptionT M A := fmap Some ma.

Instance MonadTrans_OptionT : MonadTrans OptionT :=
{
    is_monad := @Monad_OptionT;
    lift := @lift_OptionT;
}.
Proof.
  all: cbn; unfold lift_OptionT, ret_OptionT, bind_OptionT; monad.
Defined.