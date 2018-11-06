Require Import HSLib.Base.
Require Import Control.Monad.

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
    get_put' :
      forall s : S,
        get >> put s = put s;
    get_get :
      forall (A : Type) (k : S -> S -> M A),
        get >>= (fun s : S => get >>= k s) = get >>= fun s : S => k s s
}.

Hint Rewrite @put_put @put_get @get_put @get_get : HSLib.

Section MonadState_funs.

Variables
  (S : Type)
  (M : Type -> Type)
  (inst : Monad M)
  (inst' : MonadState S M inst).

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
  intros. assert (H := put_get). unfold gets. specialize (H s).
  rewrite ?constrA_spec, <- bind_assoc, H, bind_assoc, bind_pure_l in *.
  reflexivity.
Qed.

Lemma modify_put :
  forall (f : S -> S) (s : S),
    modify f >> put s = put s.
Proof.
  intros. assert (H := put_put). assert (H' := get_put).
  unfold modify in *. rewrite constrA_spec in *.
  rewrite bind_assoc.
  replace (fun x : S => put (f x) >>= (fun _ : unit => put s))
     with (fun x : S => put (f x) >> put s).
    Focus 2. ext x. rewrite put_put.
Restart.
  unfold modify. intros.
Abort.
 (* H. reflexivity.
    replace (fun x : S => put (f x) >> put s)
       with (fun x : S => put s).
      Focus 2. ext x. rewrite put_put. reflexivity.
      assert (H'' := get_put'). unfold constrA in H''. rewrite H''.
        reflexivity.
Qed.

Lemma modify_get :
  forall f : S -> S,
    modify f >> get = fmap f get.
Proof.
  intros. unfold modify, bind_. rewrite bind_assoc.
Abort.*)

End MonadState_funs.