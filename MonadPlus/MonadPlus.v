Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadBind.MonadInst.
Require Import HSLib.Alternative.Alternative.

Require Import HSLib.Instances.Option.
Require Import HSLib.Instances.ListInst.

Require Import Arith.

Class MonadPlus (M : Type -> Type) : Type :=
{
    is_monad :> Monad M;
    is_alternative :> Alternative M
}.

Section MonadPlusFuns.

Variable M : Type -> Type.
Variable inst : MonadPlus M.
Variables A B C : Type.

Definition mfilter (f : A -> bool) (ma : M A) : M A :=
  ma >>= fun a : A => if f a then ret a else aempty.

(*Fixpoint msum (lma : list (M A)) : M A :=
match lma with
    | [] => aempty
    | h :: t => aplus h (msum t)
end.*)

End MonadPlusFuns.

Arguments mfilter [M] [inst] [A] _ _.
(*Arguments msum [M] [inst] [A] _.*)

Instance MonadPlusOption : MonadPlus option :=
{
    is_monad := MonadOption;
    is_alternative := AlternativeOption
}.

Instance MonadPlusList : MonadPlus list :=
{
    is_monad := MonadList;
    is_alternative := AlternativeList
}.

Fixpoint aux (n k : nat) : list nat :=
match n with
    | 0 => [k]
    | S n' => k :: aux n' (S k)
end.

Definition I (a b : nat) : list nat := aux (b - a) a.

Compute do
  a <- I 1 35;
  b <- I 1 35;
  c <- I 1 35;
  guard (beq_nat (a * a + b * b) (c * c));;
  ret (a, b, c).

Eval compute in mfilter (fun _ => true) (I 1 10).
Eval compute in mfilter (fun _ => false) (Some 42).

(*Eval compute in asum [[2; 42]; [4; 44]].*)

Compute zipWithA
  (fun _ _ => [true; false]) [1; 2; 3] [4; 5; 6; 7].