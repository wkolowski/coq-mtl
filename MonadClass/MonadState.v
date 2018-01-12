Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.MonadBind.Monad.

Class MonadState (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    get : M S;
    put : S -> M unit;
    put_put :
      forall s1 s2 : S, put s1 >> put s2 = put s2;
    put_get :
      forall s : S, put s >> get = put s >> ret s;
    get_put :
      get >>= put = ret tt;
    get_put' :
      forall s : S,
        get >> put s = put s;
    get_get :
      forall (A : Type) (k : S -> S -> M A),
        get >>= (fun s : S => get >>= k s) = get >>= fun s : S => k s s
}.

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
      ret a.

Definition modify (f : S -> S) : M unit :=
  do
    s <- get;
    put $ f s.

Definition gets {A : Type} (f : S -> A) : M A :=
  do
    s <- get;
    ret $ f s.

Lemma put_gets :
  forall (A : Type) (s : S) (f : S -> A),
    put s >> gets f = put s >> ret (f s).
Proof.
  intros. assert (H := put_get). unfold gets, bind_ in *.
  rewrite <- assoc, H, assoc, bind_ret_l. reflexivity.
Qed.

Lemma modify_put :
  forall (f : S -> S) (s : S),
    modify f >> put s = put s.
Proof.
  intros. assert (H := put_put). assert (H' := get_put).
  unfold modify, bind_ in *.
  rewrite assoc.
  replace (fun x : S => put (f x) >>= (fun _ : unit => put s))
     with (fun x : S => put (f x) >> put s).
    Focus 2. ext x. rewrite put_put, H. reflexivity.
    replace (fun x : S => put (f x) >> put s)
       with (fun x : S => put s).
      Focus 2. ext x. rewrite put_put. reflexivity.
      assert (H'' := get_put'). unfold bind_ in H''. rewrite H''.
        reflexivity.
Qed.

Lemma modify_get :
  forall f : S -> S,
    modify f >> get = fmap f get.
Proof.
  intros. unfold modify, bind_. rewrite assoc.
Abort.

End MonadState_funs.