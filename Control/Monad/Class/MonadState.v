From CoqMTL Require Export Control.Monad.

(** A monad which has access to some kind of state. It supports two
    operations: [put] and [get], which satisfy the following laws:
    - [put_put] - putting twice in a row doesn't make sense, because
      it's the same as only the second [put]
    - [put_get] - if we [put] and then [get], we know that we will
      get back the state that we put in
    - [get_put] - if we [get] and then [put], the state doesn't change
    - [get_get] - if we [get] twice in a row and feed the states to
      some computation, it's just like we used [get] only once and
      copied the state
*)
Class MonadState
  (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
  get : M S;
  put : S -> M unit;
  put_put :
    forall s1 s2 : S, put s1 >> put s2 = put s2;
  put_get :
    forall s : S, put s >> get = put s >> pure s;
  get_put :
    get >>= put = pure tt;
  get_get :
    forall (A : Type) (k : S -> S -> M A),
      get >>= (fun s : S => get >>= k s) =
      get >>= fun s : S => k s s
}.

#[global] Hint Rewrite @put_put @put_get @get_put @get_get : CoqMTL.

Section MonadStateLaws_bind.

Variables
  (S : Type)
  (M : Type -> Type)
  (instM : Monad M)
  (instMS : MonadState S M instM).

(** The primed versions of laws are a bit expanded to ease rewriting in
    some places. *)
Lemma put_put' :
  forall s1 s2 : S, put s1 >>= (fun _ => put s2) = put s2.
Proof.
  intros. rewrite <- constrA_spec. apply put_put.
Qed.

Lemma put_put'' :
  forall (A : Type) (f : unit -> M A) (s1 s2 : S),
    put s1 >>= (fun _ : unit => put s2 >>= f) = put s2 >>= f.
Proof.
  intros. rewrite <- bind_assoc, put_put'. reflexivity.
Qed.

Lemma put_get' :
  forall s : S,
    put s >>= (fun _ => get) =
    put s >>= (fun _ => pure s).
Proof.
  intros. rewrite <- constrA_spec, put_get, constrA_spec. reflexivity.
Qed.

End MonadStateLaws_bind.

#[global] Hint Rewrite put_put' put_put'' put_get' : CoqMTL.

Set Implicit Arguments.

(** Some functions which can be found in the Haskell standard library:
    [state], [modify] and [gets]. They satisfy laws similar to the ones
    for [get] and [put]. *)
Section MonadState_funs.

Variables
  (S : Type)
  (M : Type -> Type)
  (instM : Monad M)
  (instMS : MonadState S M instM).

Definition state {A : Type} (f : S -> (A * S)%type) : M A :=
  do
    s <- get;
    let '(a, s') := f s in
    do
      put s';;
      pure a.

Definition modify (f : S -> S) : M unit :=
  do
    s <- get;
    put $ f s.

Definition gets {A : Type} (f : S -> A) : M A :=
  do
    s <- get;
    pure $ f s.

Hint Rewrite @constrA_spec : CoqMTL.

Lemma put_gets :
  forall (A : Type) (s : S) (f : S -> A),
    put s >> gets f = put s >> pure (f s).
Proof.
  intros. unfold gets.
  rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc, bind_pure_l.
  reflexivity.
Qed.

Lemma modify_put :
  forall (f : S -> S) (s : S),
    modify f >> put s = put s.
Proof.
  intros. unfold modify. hs.
  replace (put s) with (pure tt >>= fun _ => put s) by hs.
  rewrite <- get_put, bind_assoc. f_equal.
  ext s'. rewrite <- !bind_assoc, (put_get' _ _ _ _ (f s')).
  hs.
Qed.

End MonadState_funs.

Arguments state {S M instM instMS A}.
Arguments modify {S M instM instMS}.
Arguments gets {S M instM instMS A}.
Arguments put_gets {S M instM instMS A}.
Arguments modify_put {S M instM instMS}.

(*
From CoqMTL Require Import Control.Monad.Trans.

#[refine]
#[export]
Instance MonadState_MonadTrans
  (T : (Type -> Type) -> Type -> Type) (instT : MonadTrans T)
  (M : Type -> Type) (instM : Monad M)
  (S : Type) (instMS : MonadState S M instM)
  : MonadState S (T M) (is_monad _ instM) :=
{
  get := lift get;
  put := put .> lift;
}.
Proof.
  Focus 4. intros. Print MonadTrans.
  Print MonadTrans.
  rewrite lift_constrA, ask_ask. reflexivity.
Defined.
*)