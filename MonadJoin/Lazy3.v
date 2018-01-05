Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Export HSLib.MonadJoin.Monad.

Definition Lazy (A : Type) : Type := unit -> A.

Definition delay {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition force {A : Type} (la : Lazy A) : A :=
  la tt.

Definition fmap_Lazy {A B : Type} (f : A -> B) (la : Lazy A) : Lazy B :=
  fun _ => f (la tt).

Instance FunctorLazy : Functor Lazy :=
{
    fmap := @fmap_Lazy;
}.
Proof.
  intro. unfold id, fmap_Lazy. ext la. ext u. destruct u. reflexivity.
  intros. unfold compose, fmap_Lazy. ext la. reflexivity.
Defined.

Definition ret_Lazy {A : Type} (a : A) : Lazy A :=
  fun _ => a.

Definition bind_Lazy
  {A B : Type} (la : Lazy A) (f : A -> Lazy B) : Lazy B :=
    f (la tt).

Definition join_Lazy {A : Type} (lla : Lazy (Lazy A)) : Lazy A :=
  lla tt.

Instance MonadLazy : Monad Lazy :=
{
    ret := @ret_Lazy;
    join := @join_Lazy;
}.
Proof.
  all: try reflexivity.
  cbn. intros. unfold compose, ret_Lazy, join_Lazy, fmap_Lazy.
    ext la; ext u. destruct u. reflexivity.
Defined.

Eval lazy in
  delay 5 >>= fun n : nat =>
  delay 2 >>= fun m : nat => delay (n * m).

Eval lazy in
  delay 42 >>= fun n : nat => delay (2 * n).