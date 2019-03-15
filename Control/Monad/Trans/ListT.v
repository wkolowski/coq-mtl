Require Import Control.All.
Require Import Control.Monad.Trans.
Require Import Control.Monad.Class.All.

Definition ListT
  (M : Type -> Type) (A : Type) : Type :=
    forall X : Type, M X -> (A -> M X -> M X) -> M X.

(** Modified version of list notations from standard library. *)
Module ListT_Notations.

Notation "[[ ]]" :=
  (fun X nil _ => nil).
Notation "[[ x ]]" :=
  (fun X nil cons => cons x nil).
Notation "[[ x ; y ; .. ; z ]]" :=
  (fun X nil cons => cons x (cons y .. (cons z nil) ..)).

End ListT_Notations.

Export ListT_Notations.

Definition fmap_ListT
  {M : Type -> Type} {inst : Functor M} {A B : Type}
  (f : A -> B) (l : ListT M A) : ListT M B :=
    fun (X : Type) (nil : M X) (cons : B -> M X -> M X) =>
      l X nil (fun h t => cons (f h) t).

Instance Functor_ListT
  (M : Type -> Type) (inst : Functor M) : Functor (ListT M) :=
{
    fmap := @fmap_ListT M inst
}.
Proof. all: reflexivity. Defined.

Definition pure_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (x : A) : ListT M A :=
    fun (X : Type) (nil : M X) (cons : A -> M X -> M X) => cons x nil.

Definition ap_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mfs : ListT M (A -> B)) (mxs : ListT M A) : ListT M B :=
    fun X nil cons =>
      mfs X nil (fun f fs => fmap f mxs X fs cons).

Global Instance Applicative_ListT
  (M : Type -> Type) (inst : Monad M) : Applicative (ListT M) :=
{
    is_functor := Functor_ListT M inst;
    pure := @pure_ListT M inst;
    ap := @ap_ListT M inst;
}.
Proof. all: reflexivity. Defined.

Definition aempty_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) : ListT M A :=
    fun X nil cons => nil.

Definition aplus_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (ml1 ml2 : ListT M A)
    : ListT M A := fun X nil cons => ml1 X (ml2 X nil cons) cons.

Instance Alternative_ListT
  (M : Type -> Type) (inst : Monad M) : Alternative (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    aempty := aempty_ListT M inst;
    aplus := aplus_ListT M inst;
}.
Proof. all: reflexivity. Defined.

Definition bind_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mla : ListT M A) (f : A -> ListT M B) : ListT M B :=
    fun X nil cons => mla X nil (fun h t => f h X t cons).

Instance Monad_ListT
  (M : Type -> Type) (inst : Monad M) : Monad (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    bind := @bind_ListT M inst
}.
Proof. all: reflexivity. Defined.

Definition lift_ListT
  {M : Type -> Type} {inst : Monad M} (A : Type) (ma : M A) : ListT M A :=
    fun X nil cons => ma >>= fun a : A => cons a nil.

Hint Unfold pure_ListT bind_ListT lift_ListT : HSLib.

Instance MonadTrans_ListT : MonadTrans ListT :=
{
    is_monad := @Monad_ListT;
    lift := @lift_ListT;
}.
Proof. all: monad. Defined.

Definition fail_ListT
  {M : Type -> Type} {inst : Monad M} {A : Type} : ListT M A := [[]].

Hint Unfold fail_ListT : HSLib.

Instance MonadFail_ListT
  (M : Type -> Type) (inst : Monad M)
  : MonadFail (ListT M) (Monad_ListT M inst) :=
{
    fail := @fail_ListT M inst
}.
Proof. reflexivity. Defined.

Instance MonadAlt_ListT
  (M : Type -> Type) (inst : Monad M)
  : MonadAlt (ListT M) (Monad_ListT M inst) :=
{
    choose := @aplus_ListT M inst
}.
Proof. all: reflexivity. Defined.

Instance MonadNondet_ListT
  (M : Type -> Type) (inst : Monad M)
  : MonadNondet (ListT M) (Monad_ListT M inst) :=
{
    instF := MonadFail_ListT M inst;
    instA := MonadAlt_ListT M inst;
}.
Proof. all: reflexivity. Defined.

Instance MonadExcept_ListT
  (M : Type -> Type) (inst : Monad M) (inst' : MonadExcept M inst)
  : MonadExcept (ListT M) (Monad_ListT M inst) :=
{
    instF := @MonadFail_ListT M inst;
    catch :=
      fun A x y =>
        fun X nil cons => catch (x X nil cons) (y X nil cons)
}.
Proof.
  all: intros; ext X; ext nil; ext cons; cbn.
    unfold fail_ListT.
Abort.

Instance MonadReader_ListT
  (E : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadReader E M inst)
  : MonadReader E (ListT M) (Monad_ListT M inst) :=
{
    ask :=
      fun X nil cons => ask >>= (fun e => cons e nil)
}.
Proof.
  ext X. ext nil. ext cons. cbn. unfold fmap_ListT, const, id.
  rewrite <- constrA_spec, constrA_bind_assoc, ask_ask.
  reflexivity.
Defined.

Instance MonadState_ListT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadState S (ListT M) (Monad_ListT M inst) :=
{
    get := fun X nil cons => get >>= (fun s => cons s nil);
    put := fun s X nil cons => put s >> cons tt nil;
}.
Proof.
  all: intros; ext3 X nil cons; cbn.
    unfold fmap_ListT, const, id.
      rewrite <- constrA_assoc, put_put. reflexivity.
    unfold fmap_ListT, pure_ListT.
      rewrite constrA_bind_assoc, put_get, <- constrA_bind_assoc, bind_pure_l.
      reflexivity.
    unfold bind_ListT, pure_ListT.
      replace (fun s : S => put s >> cons tt nil)
         with (fun s : S => put s >>= fun _ => cons tt nil).
        rewrite <- (bind_assoc _ _ _ get put), get_put, bind_pure_l.
        reflexivity.
      ext s. rewrite constrA_spec. reflexivity.
    unfold bind_ListT, pure_ListT.
      rewrite get_get. reflexivity.
Defined.

Instance MonadStateNondet_ListT
  (S : Type) (M : Type -> Type)
  (inst : Monad M) (inst' : MonadState S M inst)
  : MonadStateNondet S (ListT M) (Monad_ListT M inst) :=
{
    instS := MonadState_ListT S M inst inst';
    instN := MonadNondet_ListT M inst;
}.
Proof.
  intros. rewrite constrA_spec. cbn. compute.
    ext X. ext nil. ext cons. admit. (* Induction would do *)
  intros. cbn. compute. ext X. ext nil. ext cons.
Abort.

Instance MonadFree_ListT
  (F : Type -> Type) (instF : Functor F)
  (M : Type -> Type) (instM : Monad M) (instMF : MonadFree F M instF instM)
  : MonadFree F (ListT M) instF (Monad_ListT M instM) :=
{
    wrap :=
      fun A fma X nil cons =>
        wrap (fmap (fun l => l X nil cons) fma)
}.
Proof.
  intros A B f x. ext3 X nil cons.
  cbn. unfold bind_ListT, pure_ListT.
  rewrite <- !fmap_comp'. unfold compose.
  reflexivity.
Defined.