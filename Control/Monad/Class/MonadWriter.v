From CoqMTL Require Export Control.Monad.

From CoqMTL Require Export Misc.Monoid.

(** For now [pass] is not present because I can't think of a law for it. *)
Class MonadWriter (W : Monoid) (M : Type -> Type) (inst : Monad M) : Type :=
{
    tell : W -> M unit;
    listen : forall {A : Type}, M A -> M (A * W)%type;
(*    pass : forall {A : Type}, M (A * (W -> W))%type -> M A;*)
    listen_pure :
      forall (A : Type) (a : A), listen (pure a) = pure (a, neutr);
(*    listen_tell :
      forall (w : W), listen (tell w) = pure (tt, w);*)
    listen_listen :
      forall (A : Type) (ma : M A),
        listen (listen ma) =
        fmap (fun '(a, w) => ((a, w), neutr)) (listen ma);
(*    listen_bind :
      forall (A B : Type) (ma : M A) (f : A -> M B),
        listen (ma >>= f) =
        listen ma >>= fun '(a, w) => fmap (fun b => (b, w)) (f a)*)
}.

#[global] Hint Rewrite @listen_pure (*@listen_tell*) @listen_listen : CoqMTL.

(*
Check
  forall
    (W : Monoid) (M : Type -> Type) (inst : Monad M) (inst' : MonadWriter W M inst)
    (A : Type) (m : M (A * (W -> W))%type),
    listen (pass m) = @bind M inst _ _ m (fun '(a, f) => fmap f (pure a)).
*)

Section MonadWriterFuns.

Variables
  (W : Monoid)
  (M : Type -> Type)
  (inst : Monad M)
  (inst' : MonadWriter W M inst).

Definition listens {A X : Type} (f : W -> X) (ma : M A) : M (A * X)%type :=
  fmap (fun '(a, w) => (a, f w)) (listen ma).

(*
-- | @'censor' f m@ is an action that executes the action @m@ and
-- applies the function @f@ to its output, leaving the return value
-- unchanged.
--
-- * @'censor' f m = 'pass' ('liftM' (\\x -> (x,f)) m)@
censor :: MonadWriter w m => (w -> w) -> m a -> m a
censor f m = pass $ do
    a <- m
    return (a, f)
*)

End MonadWriterFuns.