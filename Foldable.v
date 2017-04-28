Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Monoid.

Require Import Arith.

Class Foldable (T : Type -> Type) : Type :=
{
    foldr : forall {A B : Type}, (A -> B -> B) -> B -> T A -> B;
    foldl : forall {A B : Type}, (B -> A -> B) -> B -> T A -> B;
    foldMap : forall {A : Type} {M : Monoid}, (A -> M) -> T A -> M
}.

Section FoldableFuns.

Variable A B C : Type.
Variable T : Type -> Type.
Variable _inst : Foldable T.
Variable M : Monoid.

Definition fold (tm : T M) : M := foldr op neutr tm.

Definition isEmpty (ta : T A) : bool :=
    foldr (fun _ _ => false) true ta.

Definition size (ta : T A) : nat :=
    foldr (fun _ n => S n) 0 ta.

Definition toList (ta : T A) : list A :=
    foldr (fun h t => h :: t) [] ta.

Definition elem (cmp : A -> A -> bool) (a : A) (ta : T A) : bool :=
    foldr (fun x y => if cmp a x then true else y) false ta.

Definition maxF (tn : T nat) : nat :=
    foldr (fun n m => if leb n m then m else n) 0 tn.

Definition maxBy (cmp : A -> A -> bool) (dflt : A) (ta : T A) : A :=
    foldr (fun x xs => if cmp x xs then xs else x) dflt ta.

Definition minBy (cmp : A -> A -> bool) (dflt : A) (ta : T A) : A :=
    maxBy (fun a a' => negb (cmp a a')) dflt ta.

Definition andF (tb : T bool) : bool :=
    foldr (fun p q => andb p q) true tb.

Definition orF (tb : T bool) : bool :=
    foldr (fun p q => orb p q) false tb.

Definition allF (f : A -> bool) (ta : T A) : bool :=
    foldr (fun x xs => andb (f x) xs) true ta.

Definition anyF (f : A -> bool) (ta : T A) : bool :=
    foldr (fun x xs => orb (f x) xs) false ta.

Definition findFirst (f : A -> bool) (ta : T A) : option A :=
    foldr (fun x xs => if f x then Some x else xs) None ta.

Definition count (f : A -> bool) (ta : T A) : nat :=
    foldr (fun x n => if f x then S n else n) 0 ta.

Definition findAll (f : A -> bool) (ta : T A) : list A :=
    foldr (fun x xs => if f x then x :: xs else xs) [] ta.

End FoldableFuns.

Arguments isEmpty [A] [T] [_inst] _.
Arguments size [A] [T] [_inst] _.
Arguments toList [A] [T] [_inst] _.
Arguments elem [A] [T] [_inst] _ _ _.
Arguments maxF [T] [_inst] _.
Arguments maxBy [A] [T] [_inst] _ _ _.
Arguments minBy [A] [T] [_inst] _ _ _.
Arguments maxBy [A] [T] [_inst] _ _ _.
Arguments findFirst [A] [T] [_inst] _ _.
Arguments count [A] [T] [_inst] _ _.
Arguments findAll [A] [T] [_inst] _ _.
Arguments andF [T] [_inst] _.
Arguments orF [T] [_inst] _.
Arguments allF [A] [T] [_inst] _ _.
Arguments anyF [A] [T] [_inst] _ _.

Instance FoldableOption : Foldable option :=
{
    foldr := fun (A B : Type) (f : A -> B -> B) (dflt : B) (oa : option A) =>
        match oa with
            | None => dflt
            | Some a => f a dflt
        end;
    foldl := fun (A B : Type) (f : B -> A -> B) (dflt : B) (oa : option A) =>
        match oa with
            | None => dflt
            | Some a => f dflt a
        end;
    foldMap := fun (A : Type) (M : Monoid) (f : A -> M) (oa : option A) =>
        match oa with
            | None => neutr
            | Some a => f a
        end
}.

Eval compute in isEmpty (None).
Eval compute in size (Some 42).
Eval compute in toList (Some 5).
Eval compute in elem beq_nat 2 (Some 2).
Eval compute in maxF (Some 42).

Instance FoldableList : Foldable list :=
{
    foldr := fun A B : Type => @fold_right B A;
    foldl := fun (A B : Type) (f : B -> A -> B) (b : B) (la : list A) =>
        @fold_left B A f la b;
    foldMap := fix foldMap (A : Type) (M : Monoid) (f : A -> M) (la : list A) :=
        match la with
            | [] => neutr
            | h :: t => op (f h) (foldMap A M f t)
        end
}.

Instance FoldableSum (E : Type) : Foldable (sum E) :=
{
    foldr := fun (A B : Type) (f : A -> B -> B) (dflt : B) (ea : sum E A) =>
        match ea with
            | inl _ => dflt
            | inr a => f a dflt
        end;
    foldl := fun (A B : Type) (f : B -> A -> B) (dflt : B) (ea : sum E A) =>
        match ea with
            | inl _ => dflt
            | inr a => f dflt a
        end;
    foldMap := fun (A : Type) (M : Monoid) (f : A -> M) (ea : sum E A) =>
        match ea with
            | inl _ => neutr
            | inr a => f a
        end
}.

Eval compute in size (inr 5).
Eval compute in maxF [1; 2; 3].
Eval compute in findFirst (beq_nat 42) [1; 3; 5; 7; 11; 42].
Eval compute in count (leb 10) [1; 3; 5; 7; 11; 42].

Inductive BTree (A : Type) : Type :=
    | Empty : BTree A
    | Node : A -> BTree A -> BTree A -> BTree A.
Print Foldable.

Instance FoldableBTree : Foldable BTree :=
{
    foldMap := fix foldMap (A : Type) (M : Monoid) (f : A -> M) (bta : BTree A) :=
        match bta with
            | Empty => neutr
            | Node v l r => op (f v) (op (foldMap A M f l) (foldMap A M f r))
        end
}.
Abort.