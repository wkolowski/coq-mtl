Require Import HSLib.Base.
Require Import Control.Monad.

Require Import Control.Monad.Class.MonadFail.

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

Hint Rewrite @catch_fail_l @catch_fail_r @catch_assoc @catch_pure : HSLib.