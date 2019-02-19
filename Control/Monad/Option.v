Require Import Control.

Definition Option (A : Type) : Type := option A.

Definition fmap_Option
  {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Hint Unfold Option fmap_Option : HSLib.

Instance FunctorOption : Functor option :=
{
    fmap := @fmap_Option
}.
Proof. all: monad. Defined.

Definition pure_Option := @Some.

Definition ap_Option
  {A B : Type} (of : option (A -> B)) (oa : option A) : option B :=
match of, oa with
    | Some f, Some a => Some (f a)
    | _, _ => None
end.

Hint Unfold pure_Option ap_Option : HSLib.

Instance ApplicativeOption : Applicative option :=
{
    is_functor := FunctorOption;
    pure := pure_Option;
    ap := @ap_Option
}.
Proof. all: monad. Defined.

Definition aempty_Option {A : Type} : option A := None.

Definition aplus_Option {A : Type} (x y : option A) : option A :=
match x, y with
    | None, y => y
    | _, _ => x
end.

Hint Unfold aempty_Option aplus_Option : HSLib.

Instance AlternativeOption : Alternative option :=
{
    is_applicative := ApplicativeOption;
    aempty := @aempty_Option;
    aplus := @aplus_Option
}.
Proof. all: monad. Defined.

Definition bind_Option 
  {A B : Type} (oa : option A) (f : A -> option B) : option B :=
match oa with
    | None => None
    | Some a => f a
end.

Hint Unfold bind_Option : HSLib.

Instance CommutativeApplicative_Option :
  CommutativeApplicative _ ApplicativeOption.
Proof.
  split. destruct u, v; compute; reflexivity.
Qed.

Instance MonadOption : Monad option :=
{
    is_applicative := ApplicativeOption;
    bind := @bind_Option
}.
Proof. all: monad. Defined.

Instance MonadPlus_Option : MonadPlus option :=
{
    is_monad := MonadOption;
    is_alternative := AlternativeOption;
}.
Proof. all: hs. Defined.

Definition foldMap_Option
  {A : Type} {M : Monoid} (f : A -> M) (oa : option A) : M :=
match oa with
    | None => neutr
    | Some a => f a
end.

Hint Unfold foldMap_Option : HSLib.

Instance FoldableOption : Foldable option :=
{
    foldMap := @foldMap_Option
}.
Proof. monad. Defined.

Require Import Control.Monad.Class.All.

Definition fail_Option {A : Type} : option A := None.

Instance MonadFail_Option : MonadFail option MonadOption :=
{
    fail := @fail_Option
}.
Proof. intros. compute. reflexivity. Defined.