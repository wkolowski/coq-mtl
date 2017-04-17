Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export HSLib.MonadJoin.Monad.
Require Export HSLib.Functor.FunctorInst.

(** * Option *)
Instance MonadOption : Monad option :=
{
    is_functor := FunctorOption;
    ret := Some;
    join := fun (A : Type) (opt : option (option A)) =>
      match opt with
        | Some (Some x) => Some x
        | _ => None
      end
}.
Proof.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt as [[[ssx |] |] |]; auto.
  unfold compose; simpl; intros. extensionality opt.
    destruct opt; auto.
Defined.

Eval compute in (fun _ => Some 5) >=> (fun n => Some (n + 6)).
Eval compute in Some 4 >>= fun n : nat => Some (2 * n).

Eval compute in liftM2 plus (Some 2) (Some 4).
Eval compute in liftM2 plus (Some 42) None.

(** * List *)
Fixpoint joinList {A : Type} (lla : list (list A)) : list A :=
match lla with
  | [] => []
  | hl :: tll => hl ++ joinList tll
end.

Instance MonadList : Monad list :=
{
    ret := fun (A : Type) (a : A) => [a];
    join := @joinList
}.
Proof.
  intro. extensionality lla. induction lla as [| h t];
  unfold compose in *; simpl in *.
    trivial.
    rewrite IHt. induction h; simpl.
      trivial.
      rewrite <- app_assoc. rewrite IHh. trivial.
  intro. extensionality lla. induction lla as [| h t];
  unfold compose in *; simpl in *.
    trivial.
    f_equal. rewrite <- IHt. trivial. 
Defined.

Definition head {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | [_] => Some []
    | h :: t => liftM2 (@cons A) (ret h) (init t)
end.

Eval compute in init [1; 2; 3].

Eval simpl in filterM (fun _ => [true; false]) [1; 2; 3].

Eval simpl in replicateM _ _ 5 [1; 2].

Eval simpl in sequence [[1]; [2]].

Definition joinE {A B : Type} (x : sum A (sum A B)) : sum A B :=
match x with
    | inl a => inl a
    | inr x' =>
        match x' with
            | inl a => inl a
            | inr b => inr b
        end
end.

Instance MonadEither (A : Type) : Monad (sum A) :=
{
    is_functor := FunctorSum A;
    ret := @inr A;
    join := @joinE A
}.
Proof.
  intro B. extensionality x.
    destruct x as [a | [a | [a | b]]]; compute; trivial.
  intro B. extensionality x.
    destruct x as [a | b]; compute; trivial.
Defined.

Eval simpl in sequence [inr 42; inr 5; inr 10].
Eval simpl in sequence [inr 42; inr 5; inr 10; inl (fun n : nat => 2 * n)].

Eval simpl in foldM _ _ (fun n m => inl (plus n m)) 0 [1; 2; 3].
