Require Export Control.Monad.

Class MonadError
  (E : Type) (M : Type -> Type) (inst : Monad M)  : Type :=
{
    throw : forall {A : Type}, E -> M A;
    catch : forall {A : Type}, M A -> M A -> M A;
    catch_throw_l :
      forall (A : Type) (e : E) (x : M A),
        catch (throw e) x = x;
    catch_throw_r :
      forall (A : Type) (x : M A) (e : E),
        catch x (throw e) = x;
    catch_assoc :
      forall (A : Type) (x y z : M A),
        catch (catch x y) z = catch x (catch y z);
    catch_pure :
      forall (A : Type) (x : A) (h : M A),
        catch (pure x) h = pure x;
}.

Hint Rewrite @catch_throw_l @catch_throw_r @catch_assoc @catch_pure : HSLib.