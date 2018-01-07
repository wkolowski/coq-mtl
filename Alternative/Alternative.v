Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Functor.Functor.
Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Foldable.

Class Alternative (F : Type -> Type) : Type :=
{
    is_applicative :> Applicative F;
    aempty : forall {A : Type}, F A;
    aplus : forall {A : Type}, F A -> F A -> F A;
    id_left :
      forall (A : Type) (fa : F A),
        aplus aempty fa = fa;
    id_right :
      forall (A : Type) (fa : F A),
        aplus fa aempty = fa;
    aplus_assoc :
      forall (A : Type) (x y z : F A),
        aplus x (aplus y z) = aplus (aplus x y) z
}.

Coercion is_applicative : Alternative >-> Applicative.

Module AlternativeNotations.

Notation "x <|> y" := (aplus x y)
  (left associativity, at level 40).

End AlternativeNotations.

Export AlternativeNotations.

Section AlternativeFuns.

Variable F : Type -> Type.
Variable instF : Alternative F.

Variable T : Type -> Type.
Variable instT : Foldable T.

Variables A B C : Type.

Definition asum : T (F A) -> F A := foldr aplus aempty.

Definition aFromOption (oa : option A) : F A :=
match oa with
    | None => aempty
    | Some a => ret a
end.

Fixpoint aFromList (la : list A) : F A :=
match la with
    | [] => aempty
    | h :: t => ret h <|> aFromList t
end.

Definition afold (ta : T A) : F A :=
  aFromList (toListF ta).

Definition optional (x : F A) : F (option A) :=
  aplus (fmap (@Some A) x) (ret None).

Definition guard (b : bool) : F unit :=
  if b then ret tt else aempty.

End AlternativeFuns.

Arguments asum [F instF T instT A] _.
Arguments aFromOption [F instF A] _.
Arguments aFromList [F instF A] _.
Arguments afold [F instF T instT A] _.
Arguments optional [F instF A] _.
Arguments guard [F instF] _.