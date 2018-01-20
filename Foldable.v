Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.Monoid.

Require Import Arith.

Class Foldable (T : Type -> Type) : Type :=
{
    (*foldr : forall {A B : Type}, (A -> B -> B) -> B -> T A -> B;
    foldl : forall {A B : Type}, (B -> A -> B) -> B -> T A -> B;*)
    foldMap : forall {A : Type} {M : Monoid}, (A -> M) -> T A -> M;
    foldMap_law :
      forall (A : Type) (B C : Monoid) (f : A -> B) (g : B -> C),
        g neutr = neutr -> (forall x y : B, g (op x y) = op (g x) (g y)) ->
          foldMap (f .> g) = foldMap f .> g
}.

Instance Endo (A : Type) : Monoid :=
{
    carr := A -> A;
    op := @compose A A A;
    neutr := id;
}.
Proof. all: reflexivity. Defined.

Section FoldableFuns.

Variable A B C : Type.
Variable T : Type -> Type.
Variable inst : Foldable T.
Variable M : Monoid.

Definition foldr
  {A B : Type} (f : A -> B -> B) (dflt : B) (t : T A) : B :=
    @foldMap T inst A (Endo B) (fun a : A => f a) t dflt.

Definition foldl
  {A B : Type} (f : B -> A -> B) (dflt : B) (t : T A) : B :=
    @foldMap T inst A (Endo B) (fun a : A => flip f a) t dflt.

Definition fold (t : T M) : M := foldr op neutr t.

Definition isEmpty (ta : T A) : bool :=
  foldr (fun _ _ => false) true ta.

Definition size (ta : T A) : nat :=
  foldr (fun _ n => S n) 0 ta.

Definition toListF (ta : T A) : list A :=
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

Arguments foldr [T inst A B] _ _ _.
Arguments foldl [T inst A B] _ _ _.
Arguments isEmpty [A T inst] _.
Arguments size [A T inst] _.
Arguments toListF [A T inst] _.
Arguments elem [A T inst] _ _ _.
Arguments maxF [T inst] _.
Arguments maxBy [A T inst] _ _ _.
Arguments minBy [A T inst] _ _ _.
Arguments maxBy [A T inst] _ _ _.
Arguments findFirst [A T inst] _ _.
Arguments count [A T inst] _ _.
Arguments findAll [A T inst] _ _.
Arguments andF [T inst] _.
Arguments orF [T inst] _.
Arguments allF [A T inst] _ _.
Arguments anyF [A T inst] _ _.

Definition foldMap_Option
  {A : Type} {M : Monoid} (f : A -> M) (oa : option A) : M :=
match oa with
    | None => neutr
    | Some a => f a
end.

Instance FoldableOption : Foldable option :=
{
    foldMap := @foldMap_Option
}.
Proof.
  intros. ext oa. destruct oa; unfold compose; cbn; congruence.
Defined.

Eval compute in isEmpty (None).
Eval compute in size (Some 42).
Eval compute in toListF (Some 5).
Eval compute in elem beq_nat 2 (Some 2).
Eval compute in maxF (Some 42).

Fixpoint foldMap_List
  {A : Type} {M : Monoid} (f : A -> M) (l : list A) :=
match l with
    | [] => neutr
    | h :: t => op (f h) (foldMap_List f t)
end.

Instance FoldableList : Foldable list :=
{
    foldMap := @foldMap_List
}.
Proof.
  intros. ext l.
  induction l as [| h t]; unfold compose in *; cbn; congruence.
Defined.

Definition foldMap_Sum
  {E A : Type} {M : Monoid} (f : A -> M) (x : sum E A) : M :=
match x with
    | inl _ => neutr
    | inr a => f a
end.

Instance FoldableSum (E : Type) : Foldable (sum E) :=
{
    foldMap := @foldMap_Sum E
}.
Proof.
  intros. ext x. destruct x; unfold compose; cbn; congruence.
Defined.

Eval compute in size (inr 5).
Eval compute in maxF [1; 2; 3].
Eval compute in findFirst (beq_nat 42) [1; 3; 5; 7; 11; 42].
Eval compute in count (leb 10) [1; 3; 5; 7; 11; 42].

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | T : A -> BTree A -> BTree A -> BTree A.

Arguments E [A].
Arguments T [A] _ _ _.

Fixpoint foldMap_BTree
  {A : Type} {M : Monoid} (f : A -> M) (t : BTree A) :=
match t with
    | E => neutr
    | T v l r => op (f v) (op (foldMap_BTree f l) (foldMap_BTree f r))
end.

Instance FoldableBTree : Foldable BTree :=
{
    foldMap := @foldMap_BTree
}.
Proof.
  intros. ext t.
  induction t as [| v l IHl r IHr]; unfold compose in *; cbn; congruence.
Defined.