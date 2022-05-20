Require Export Control.Monad.
Require Export Control.Monad.Class.MonadFail.

(** An exception monad. [catch] is an associative operation that models
    catching exceptions. The first argument is the computation to be
    performed and the second argument is the handler. Laws can be
    interpreted like this:
    - [catch_fail_l]: catching a [fail] results in running the handler
    - [catch_fail_r]: if the handler is a failure, the computation is
      equivalent to one without [catch]
    - [catch_pure]: if a computation doesn't throw an exception, then
      the handler won't be run
*)
Class MonadExcept
  (M : Type -> Type) (inst : Monad M)  : Type :=
{
    instF :> MonadFail M inst;
    catch : forall {A : Type}, M A -> M A -> M A;
    catch_fail_l :
      forall (A : Type) (x : M A),
        catch fail x = x;
    catch_fail_r :
      forall (A : Type) (x : M A),
        catch x fail = x;
    catch_assoc :
      forall (A : Type) (x y z : M A),
        catch (catch x y) z = catch x (catch y z);
    catch_pure :
      forall (A : Type) (x : A) (h : M A),
        catch (pure x) h = pure x;
}.

Coercion instF : MonadExcept >-> MonadFail.

#[global] Hint Rewrite @catch_fail_l @catch_fail_r @catch_assoc @catch_pure : CoqMTL.