Add Rec LoadPath "/home/Zeimer/Code/Coq/Lambda/Materiały".

Require Export HSLib.Functor.Functor.

Instance FunctorOption : Functor option :=
{
    fmap := fun {A B : Type} (f : A -> B) (oa : option A) =>
        match oa with
            | None => None
            | Some a => Some (f a)
        end
}.
Proof.
  intros; extensionality x; destruct x; auto.
  intros; extensionality x; destruct x; auto.
Defined.

Instance FunctorList : Functor list :=
{
    fmap := map (* fix fmap {A B : Type} (f : A -> B) (l : list A) : list B :=
      match l with
        | [] => []
        | h :: t => f h :: fmap f t
      end *)
}.
Proof.
  intro. unfold id. extensionality l. induction l as [| h t]; simpl.
    reflexivity.
    f_equal. auto.
  intros. unfold compose. extensionality l. induction l as [| h t]; simpl.
    reflexivity.
    f_equal. auto.
Defined.

Eval simpl in void [1; 2; 3].

Instance FunctorSum (A : Type) : Functor (sum A) :=
{
    fmap := fun {B B' : Type} (f : B -> B') (x : sum A B) =>
        match x with
            | inl a => inl a
            | inr b => inr (f b)
        end
}.
Proof.
  intros. extensionality x. destruct x; unfold id; trivial.
  intros. extensionality x. destruct x; unfold id; trivial.
Defined.

Instance FunctorProd (A : Type) : Functor (prod A) :=
{
    fmap := fun {B B' : Type} (f : B -> B') (x : A * B) =>
        match x with | pair a b => pair a (f b) end
}.
Proof.
  intros. extensionality x. destruct x; unfold id; trivial.
  intros. extensionality x. destruct x; unfold id; trivial.
Defined.

