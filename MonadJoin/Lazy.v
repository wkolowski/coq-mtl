Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.MonadJoin.Monad.

Inductive Lazy (Z : Type) : Type :=
    | delay : Z -> Lazy Z
    | Later : forall (A : Type), (A -> Z) -> A -> Lazy Z.

Arguments delay [Z] _.
Arguments Later [Z A] _ _.

Definition force {A : Type} (la : Lazy A) : A :=
match la with
    | delay a => a
    | Later f x => f x
end.

Definition fmapL {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
match la with
    | delay v => delay (f v)
    | Later g a => Later (g .> f) a
end.

Instance FunctorLazy : Functor Lazy :=
{
    fmap := @fmapL
}.
Proof.
  intro. unfold fmapL. extensionality la. destruct la.
    unfold id. reflexivity.
    unfold id, compose. f_equal.
  intros. unfold fmapL, compose. extensionality la. destruct la.
    reflexivity.
    reflexivity.
Defined.

Definition joinL {A : Type} (lla : Lazy (Lazy A)) : Lazy A :=
match lla with
    | delay v => match v with
        | delay v' => delay v'
        | Later f v' => delay (f v')
    end
    | Later f v => f v
end.

Definition bindL {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
match la with
    | delay a => f a
    | Later g x => f (g x)
end.

Definition bindL' {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
match la with
    | delay a => f a
    | Later g x => match f (g x) with
        | delay x' => Later id x'
        | _ => f (g x)
    end
end.

Definition joinL' {A : Type} (lla : Lazy (Lazy A)) : Lazy A :=
    bindL' lla id.

Check @joinL'.

Instance MonadLazy : Monad Lazy :=
{
    is_functor := FunctorLazy;
    ret := fun {A : Type} (a : A) => delay a;
      (* @Later A A (fun x : _ => x) a; Universe problems *)
    join := @joinL
}.
Proof.
  intro; simpl. unfold fmapL, joinL. extensionality la. unfold compose.
  destruct la.
    destruct l.
      destruct l; auto.
      destruct (l a); auto.
    destruct (l a); auto.
  simpl; intros. extensionality la. destruct la. auto.
    unfold compose. simpl. unfold compose. reflexivity.
Defined.

(* I should check the version with Later as return. *)
Eval lazy in
  delay 5 >>= fun n : nat => Later (fun _ : nat => 2 * n) 42.

Eval lazy in
  Later (fun n : nat => 2 * n) 2.

Eval lazy in
  Later (fun n : nat => n + 2) 3 >>= fun n : nat =>
  Later (fun n : nat => 2 * n) n.

Eval lazy in
  Later id 5 >>= fun n : nat => Later (fun m => n * m) 3.