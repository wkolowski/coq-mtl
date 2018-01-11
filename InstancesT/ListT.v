Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.Applicative.Applicative.
Require Import HSLib.Alternative.Alternative.
Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadPlus.MonadPlus.
Require Import HSLib.MonadTrans.MonadTrans.

Require Import HSLib.Instances.All.
Require Import HSLib.MonadBind.MonadInst.

Definition ListT (M : Type -> Type) (A : Type) : Type := M (list A).

Definition fmap_ListT
  (M : Type -> Type) (inst : Functor M)
  (A B : Type) (f : A -> B) : ListT M A -> ListT M B :=
    fmap (map f).

Instance Functor_ListT
  (M : Type -> Type) (inst : Functor M) : Functor (ListT M) :=
{
    fmap := fmap_ListT M inst
}.
Proof.
  all: intros; unfold fmap_ListT.
    ext x. replace (map id) with (@id (list A)).
      rewrite fmap_pres_id. reflexivity.
      unfold id. ext l. rewrite map_id. reflexivity.
    functor. unfold compose. rewrite map_map. reflexivity.
Defined.

Definition ret_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (x : A)
    : ListT M A := ret [x].

Definition ap_ListT
  (M : Type -> Type) (inst : Monad M) (A B : Type)
  (mfs : ListT M (A -> B)) (mxs : ListT M A) : ListT M B :=
    @bind M inst _ _ mfs (fun fs =>
    @bind M inst _ _ mxs (fun xs =>
      ret $ ap_list fs xs)).


Axiom wut : False.

Instance Applicative_ListT
  (M : Type -> Type) (inst : Monad M) : Applicative (ListT M) :=
{
    is_functor := Functor_ListT M inst;
    ret := ret_ListT M inst;
    ap := ap_ListT M inst;
}.
Proof.
  all: cbn; unfold ListT, fmap_ListT, ret_ListT, ap_ListT; monad; cbn.
    rewrite app_nil_r. rewrite map_id. reflexivity.
    rewrite app_nil_r. destruct wut. (* TODO *)
    rewrite <- ap_list_exchange. cbn. reflexivity.
    rewrite app_nil_r. reflexivity.
Defined.

Definition aempty_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) : ListT M A :=
    ret [].

Definition aplus_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (ml1 ml2 : ListT M A)
    : ListT M A :=
      @bind M inst _ _ ml1 (fun l1 =>
      @bind M inst _ _ ml2 (fun l2 =>
        ret (l1 ++ l2))).

Instance Alternative_ListT
  (M : Type -> Type) (inst : Monad M) : Alternative (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    aempty := aempty_ListT M inst;
    aplus := aplus_ListT M inst;
}.
Proof.
  all: cbn; unfold ListT, aempty_ListT, aplus_ListT; monad.
    rewrite app_nil_r. reflexivity.
    rewrite app_assoc. reflexivity.
Defined.

Fixpoint bind_ListT_aux
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (f : A -> ListT M B) (l : list A) : ListT M B :=
match l with
    | [] => ret []
    | h :: t => liftA2 (@app B) (f h) (bind_ListT_aux f t)
end.

Definition bind_ListT
  {M : Type -> Type} {inst : Monad M} {A B : Type}
  (mla : ListT M A) (f : A -> ListT M B) : ListT M B :=
    @bind M inst (list A) (list B) mla (bind_ListT_aux f).

Lemma bind_ListT_aux_assoc :
  forall (M : Type -> Type) (inst : Monad M) (A B C : Type)
  (x : ListT M A) (f : A -> ListT M B) (g : B -> ListT M C),
    bind_ListT (bind_ListT x f) g =
    bind_ListT x (fun a : A => bind_ListT (f a) g).
Proof.
  intros. unfold bind_ListT. rewrite assoc. f_equal. ext la.
  gen C; gen B. clear x.
  induction la as [| ha ta]; cbn; intros.
    rewrite bind_ret_l. cbn. reflexivity.
(*
    rewrite <- ?IHta. rewrite !assoc. f_equal. ext lb.
      rewrite !assoc.
      replace (fun x : list B =>
      @ret M inst (list B) (x ++ lb) >>= @bind_ListT_aux M inst B C g)
      with (fun x : list B =>
      @bind_ListT_aux M inst B C g (x ++ lb)).
        Focus 2. ext wut. rewrite bind_ret_l. reflexivity.
        Check assoc. Check bind_ret_r.
*)
(*


      replace (fun x : list B =>
        @ret M inst (list B) (lb ++ x) >>= @bind_ListT_aux M inst B C g)
      with (fun x : list B =>
        @bind_ListT_aux M inst B C g (lb ++ x)).
          Focus 2. ext wut. rewrite bind_ret_l. reflexivity.
      Check bind_ret_r. Print bind_. rewrite IHta.
      replace (fun b : list C => @ret M inst (list C) (a ++ b)))
      with (fun lc : list C => 
*)
Abort.

Instance Monad_ListT
  (M : Type -> Type) (inst : Monad M) : Monad (ListT M) :=
{
    is_applicative := Applicative_ListT M inst;
    bind := @bind_ListT M inst
}.
Proof.
  all: cbn; unfold ListT, fmap_ListT, ret_ListT, ap_ListT, bind_ListT; intros.
    monad. unfold bind_ListT_aux, liftA2. monad.
      rewrite app_nil_r. reflexivity.
    match goal with
        | |- ?moa >>= ?f = ?moa => replace f with (@ret M inst (list A))
    end.
      monad.
      ext la. induction la; cbn.
        reflexivity.
        rewrite <- IHla. unfold liftA2. monad.
    destruct wut.
    monad. unfold compose. ext l.
      induction l; cbn; rewrite ?IHl; reflexivity.
    monad. destruct wut.
    monad. destruct wut. (* TODO *)
Defined.

Definition lift_ListT
  (M : Type -> Type) (inst : Monad M) (A : Type) (ma : M A)
    : ListT M A := ma >>= fun a : A => @ret M inst _ [a].

Instance MonadTrans_ListT : MonadTrans ListT :=
{
    is_monad := @Monad_ListT;
    lift := @lift_ListT;
}.
Proof.
  all: cbn; intros; unfold lift_ListT, ret_ListT, bind_ListT.
    monad.
    monad. unfold bind_ListT_aux, liftA2, compose. rewrite ?bind_ap, assoc.
      f_equal. destruct wut. (* TODO *)
Defined.