Require Import Monad.
Require Import MonadInst.
Require Import Alternative.

Class MonadPlus (M : Type -> Type) : Type :=
{
    is_monad :> Monad M;
    is_alternative :> Alternative M
}.

Section funs.

Variable M : Type -> Type.
Variable inst : MonadPlus M.
Variables A B C : Type.

Definition mfilter (f : A -> bool) (ma : M A) : M A :=
    ma >>= fun a : A => if f a then ret a else aempty.
(*@guard _ _ A (f a) >>= fun _ => ret a. *)

Fixpoint msum (lma : list (M A)) : M A :=
match lma with
    | [] => aempty
    | h :: t => aplus h (msum t)
end.

End funs.

Definition to_1_10 := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

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

Arguments mfilter [M] [inst] [A] _ _.
Arguments msum [M] [inst] [A] _.

Eval simpl in
    to_1_10 >>= fun a =>
    to_1_10 >>= fun b =>
    to_1_10 >>= fun c =>
    guard (beq_nat (a * a + b * b) (c * c)) >>= fun _ =>
    ret (a, b, c).

Eval compute in mfilter (fun _ => true) to_1_10.
Eval compute in mfilter (fun _ => false) (Some 42).

Eval compute in msum [[2; 42]; [4; 44]].

Eval compute in @zipWithM _ _ _ _ _
    (fun _ _ => [true; false]) [1; 2; 3] [4; 5; 6; 7].



