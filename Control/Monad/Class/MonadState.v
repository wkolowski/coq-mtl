Require Import HSLib.Base.
Require Import Control.Monad.
Require Import Control.Monad.Trans.

Class MonadState (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
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
        get >>= (fun s : S => get >>= k s) = get >>= fun s : S => k s s
}.

Hint Rewrite @put_put @put_get @get_put @get_get : HSLib.

Section MonadStateLaws_bind.

Variables
  (S : Type)
  (M : Type -> Type)
  (instM : Monad M)
  (instMS : MonadState S M instM).

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

Hint Rewrite put_put' put_put'' put_get' : HSLib.

Polymorphic Lemma bind_constrA_assoc :
  forall
    (M : Type -> Type) (inst : Monad M) 
    (A B C : Type) (x : M A) (f : A -> M B) (y : M C),
       x >>= f >> y = x >>= (fun a : A => f a >> y).
Proof.
  intros. monad.
Qed.

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

Hint Rewrite @constrA_spec : HSLib.

Lemma put_gets :
  forall (A : Type) (s : S) (f : S -> A),
    put s >> gets f = put s >> pure (f s).
Proof.
  intros. unfold gets.
  rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc, bind_pure_l.
  reflexivity.
Qed.

End MonadState_funs.

Arguments state {S M instM instMS A}.
Arguments modify {S M instM instMS}.
Arguments gets {S M instM instMS A}.

Variables
  (T : (Type -> Type) -> Type -> Type) (instT : MonadTrans T)
  (M : Type -> Type) (instM : Monad M)
  (S : Type)
  (instMF : MonadState S M instM).

Instance MonadState_MonadTrans
  : MonadState S (T M) (is_monad M instM) :=
{
    get := lift get;
    put := put .> lift;
}.
Proof.
  intros. unfold compose. rewrite lift_constrA, put_put. reflexivity.
  intros. unfold compose.
    rewrite lift_constrA, put_get, <- lift_constrA, lift_pure. reflexivity.
  rewrite <- lift_pure, <- get_put, lift_bind. reflexivity.
  intros.
  Print MonadTrans.
Abort.

Lemma modify_put :
  forall (f : S -> S) (s : S),
    modify f >> put s = put s.
Proof.
  intros.

 unfold modify.
  rewrite constrA_spec.
  rewrite bind_assoc.
  Check put_put''.
  
  Check put_put'.
  replace (fun x : S => put (f x) >>= fun _ => put s)
     with (fun _ : S => put s).
    Focus 2. ext x. rewrite put_put'. reflexivity.
    Search put.
Abort.