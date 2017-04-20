(*Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Export HSLib.MonadJoin.Monad.

Inductive Lazy (Z : Type) : Type :=
    | Now : Z -> Lazy Z
    | Later : forall (A : Type), (A -> Z) -> A -> Lazy Z.

Arguments Now [Z] _.
Arguments Later [Z] _ _ _.

Definition fmapL {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
match la with
    | Now v => Now (f v)
    | Later _ g a => Later _ (g .> f) a
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
    | Now v => match v with
        | Now v' => Now v'
        | Later _ f v' => Now (f v')
    end
    | Later _ f v => f v
end.

Definition bindL {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
match la with
    | Now a => f a
    | Later _ g x => f (g x)
end.

Definition bindL' {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
match la with
    | Now a => f a
    | Later _ g x => match f (g x) with
        | Now x' => Later _ id x'
        | _ => f (g x)
    end
end.

Definition joinL' {A : Type} (lla : Lazy (Lazy A)) : Lazy A :=
    bindL' lla id.

Check @joinL'.

Instance MonadLazy : Monad Lazy :=
{
    is_functor := FunctorLazy;
    ret := fun {A : Type} (a : A) => Now a;
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

Eval compute in Now 5 >>= fun n : nat => Later _ (fun _ : nat => 2 * n) 2.

Eval simpl in Later _ (fun n : nat => 2 * n) 2.

Eval simpl in Later _ (fun n : nat => n + 2) 3 >>= fun n : nat =>
    Later _ (fun n : nat => 2 * n) n.

Eval simpl in Later _ id 5 >>= fun n : nat => Later _ (fun m => n * m) 3.*)