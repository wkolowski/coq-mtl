Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition ListT (M : Type -> Type) (A : Type) : Type := M (list A).

Definition fmap_ListT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : ListT M A -> ListT M B :=
    fmap (fix aux (la : list A) : list B :=
    match la with
        | [] => []
        | h :: t => f h :: aux t
    end).

Instance FunctorListT (M : Type -> Type) {inst : Functor M}
    : Functor (ListT M) :=
{
    fmap := fmap_ListT
}.
Proof.
  all: intros; unfold fmap_ListT.
    replace (fmap _) with (fmap (@id (list A))).
      rewrite fmap_pres_id. reflexivity.
      f_equal. ext l. unfold id.
        induction l as [| h t]; cbn; rewrite <- ?IHt; reflexivity.
    functor.
      unfold compose in *. rewrite IHx. reflexivity.
Defined.

Definition ret_ListT
  {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : ListT M A := ret [x].

Definition bind_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mla : ListT M A) (f : A -> ListT M B) : ListT M B :=
    @bind M inst (list A) (list B) mla (fix aux (la : list A) : M (list B) :=
match la with
    | [] => ret []
    | h :: t => liftM2 (@app B) (f h) (aux t)
end).

Axiom wut : False.

Instance Monad_ListT (M : Type -> Type) {inst : Monad M}
    : Monad (ListT M) :=
{
    is_functor := FunctorListT M;
    ret := @ret_ListT M inst;
    bind := @bind_ListT M inst
}.
Proof.
  all: cbn; intros; unfold fmap_ListT, ret_ListT.
    unfold bind_ListT. rewrite bind_ret_l. unfold liftM2, ListT in *.
      rewrite <- (bind_ret_r _ (f a)) at 2. f_equal.
      ext l. rewrite bind_ret_l. f_equal. apply app_nil_r.
    unfold bind_ListT;
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (list A))
    end.
      rewrite bind_ret_r. reflexivity.
      ext la. induction la; cbn.
        reflexivity.
        rewrite <- IHla. unfold liftM2. rewrite ?bind_ret_l. reflexivity.
    unfold bind_ListT. rewrite assoc. f_equal. ext l.
      induction l as [| h t]; cbn.
        rewrite bind_ret_l. reflexivity.
        destruct wut. (* TDOO *)
    rewrite fmap_ret. reflexivity.
    unfold bind_ListT. rewrite bind_fmap. unfold compose. f_equal. ext l.
      induction l; cbn; rewrite ?IHl; reflexivity.
    unfold bind_ListT. rewrite fmap_bind. f_equal. ext la.
      induction la as [| h t]; cbn.
        rewrite fmap_ret. reflexivity.
        rewrite <- IHt. clear IHt. unfold liftM2.
          rewrite !bind_fmap, !fmap_bind. f_equal. ext lb. unfold compose.
          rewrite bind_fmap. unfold compose. rewrite fmap_bind.
          destruct wut. (* TODO *)
Defined.

Definition lift_ListT
  {M : Type -> Type} {inst : Monad M} {A : Type} (ma : M A)
    : ListT M A := ma >>= fun a : A => @ret M inst _ [a].

Instance MonadTrans_ListT : MonadTrans ListT :=
{
    is_monad := @Monad_ListT;
    lift := @lift_ListT;
}.
Proof.
  all: cbn; intros; unfold lift_ListT, ret_ListT, bind_ListT.
    rewrite bind_ret_l. reflexivity.
    rewrite !assoc. f_equal. ext a. rewrite bind_ret_l.
      unfold liftM2, compose. rewrite assoc. f_equal. ext b.
      rewrite !bind_ret_l. rewrite app_nil_r. reflexivity.
Defined.