Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.

Require Import HSLib.MonadBind.Monad.
Require Import HSLib.MonadTrans.MonadTrans.

Definition ListT (M : Type -> Type) (A : Type) : Type := M (list A).
(*
Definition fmap_ListT
  {M : Type -> Type} {inst : Functor M}
  (A B : Type) (f : A -> B) : ListT M A -> ListT M B :=
    fmap (map f).

Instance FunctorListT (M : Type -> Type) {inst : Functor M}
    : Functor (ListT M) :=
{
    fmap := fmap_ListT
}.
Proof.
  all: intros; unfold fmap_ListT.
    ext x. replace (map id) with (@id (list A)).
      rewrite fmap_pres_id. reflexivity.
      unfold id. ext l. rewrite map_id. reflexivity.
    functor. unfold compose. rewrite map_map. reflexivity.
Defined.

Definition ret_ListT
  {M : Type -> Type} {inst : Monad M} {A : Type} (x : A)
    : ListT M A := ret [x].

Fixpoint bind_ListT_aux
  {M : Type -> Type} {inst : Monad M} {A B : Type} (f : A -> ListT M B)
  (l : list A) : ListT M B :=
match l with
    | [] => ret []
    | h :: t => liftM2 (@app B) (f h) (bind_ListT_aux f t)
(*                @bind M inst _ _ (bind_ListT_aux f t) (fun l2 =>
                @bind M inst _ _ (f h) (fun l1 =>
                  ret (l1 ++ l2)))*)
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
    unfold bind_ListT. rewrite bind_ret_l. cbn. unfold liftM2, ListT in *.
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
    destruct wut.
    rewrite fmap_ret. reflexivity.
    unfold bind_ListT. rewrite bind_fmap. unfold compose. f_equal. ext l.
      induction l; cbn; rewrite ?IHl; reflexivity.
    unfold bind_ListT. rewrite fmap_bind. f_equal. ext la.
    gen g; gen f. clear x.
      induction la as [| ha ta]; cbn; intros.
        rewrite fmap_ret. cbn. reflexivity.
        rewrite <- IHta. clear IHta. unfold liftM2.
          rewrite !bind_fmap, !fmap_bind. f_equal. ext lb. unfold compose.
          rewrite fmap_bind. rewrite bind_fmap. f_equal. unfold compose.
            ext lb'. rewrite fmap_ret, map_app. reflexivity.
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
      unfold bind_ListT_aux, liftM2, compose. rewrite assoc. f_equal.
        ext b. rewrite !bind_ret_l. rewrite app_nil_r. reflexivity.
Defined.
*)