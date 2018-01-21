Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import HSLib.MonadBind.Monad.

(** * Just do It: Simple Monadic Equational Reasoning *)

(** ** 1. Introduction *)

(** ** 2. Background *)

(** ** 3. A counter example: Towers of Hanoi *)

Set Universe Polymorphism.
Set Implicit Arguments.

Section S0.

Variable M : Type -> Type.

Variable inst : Monad M.

Class MonadCount : Type :=
{
    tick : M unit;
}.

Definition skip : M unit := ret tt.

Fixpoint hanoi {inst' : MonadCount} (n : nat) : M unit :=
match n with
    | 0 => skip
    | S n' => hanoi n' >> tick >> hanoi n'
end.

Fixpoint rep (n : nat) (x : M unit) : M unit :=
match n with
    | 0 => skip
    | S n' => x >> rep n' x
end.

Require Import Arith.

Lemma bind__assoc :
  forall (A B C : Type) (ma : M A) (mb : M B) (mc : M C),
    (ma >> mb) >> mc = ma >> (mb >> mc).
Proof.
  intros. unfold bind_. rewrite assoc. reflexivity.
Qed.

Lemma rep_bind_ :
  forall (x : M unit) (n m : nat),
    rep (n + m) x = rep n x >> rep m x.
Proof.
  induction n as [| n']; cbn; intros.
    unfold skip, bind_. rewrite bind_ret_l. reflexivity.
    rewrite IHn'. rewrite bind__assoc. reflexivity.
Qed.

Lemma rep1 :
  forall x : M unit, rep 1 x = x.
Proof.
  intros. cbn. unfold skip, bind_. rewrite <- bind_ret_r.
  f_equal. ext u. destruct u. reflexivity.
Qed.

Require Import Nat.
Require Import Omega.

Theorem hanoi_rep :
  forall (inst' : MonadCount) (n : nat),
    hanoi n = rep (2 ^ n - 1) tick.
Proof.
  induction n as [| n']; cbn; try reflexivity.
  rewrite IHn', bind__assoc. rewrite <- (rep1 tick) at 2.
  rewrite <- !rep_bind_, <- plus_n_O, <- !pred_of_minus. f_equal.
  induction n' as [| n'']; cbn.
    reflexivity. erewrite (Nat.lt_succ_pred 0).
      omega.
      clear. induction n'' as [| n''']; cbn; abstract omega.
Qed.

(** ** 4. Nondeterministic computations *)

(** *** 4.1 Failure *)

Class MonadFail : Type :=
{
    fail : forall {A :  Type}, M A;
    bind_fail_l :
      forall (A B : Type) (mb : M B),
        @fail A >> mb = @fail B;
(** TODO: BEWARE! Custom laws *)
    bind_fail_l' :
      forall (A B : Type) (f : A -> M B),
        fail >>= f = fail
}.

Definition guard {inst' : MonadFail} (b : bool) : M unit :=
  if b then skip else fail.

Definition assert
  {inst' : MonadFail} {A : Type} (p : A -> bool) (ma : M A) : M A :=
  do
    a <- ma;
    guard (p a);;
    ret a.

(** *** 4.2 Choice *)

Class MonadAlt : Type :=
{
    choose : forall {A : Type}, M A -> M A -> M A;
    choose_assoc :
      forall {X : Type} (a b c : M X),
        choose (choose a b) c = choose a (choose b c);
    choose_bind :
      forall (A B : Type) (x y : M A) (f : A -> M B),
        choose x y >>= f = choose (x >>= f) (y >>= f);
}.

(** *** 4.3 Nondeterminism *)

Class MonadNondet : Type :=
{
    instF :> MonadFail;
    instA :> MonadAlt;
    choose_fail_l :
      forall (A : Type) (x : M A),
        choose fail x = x;
    choose_fail_r :
      forall (A : Type) (x : M A),
        choose x fail = x;
}.

Coercion instF : MonadNondet >-> MonadFail.
Coercion instA : MonadNondet >-> MonadAlt.

End S0.

Require Import HSLib.Instances.All.
Require Import HSLib.MonadBind.MonadInst.

Instance MonadFail_List : MonadFail MonadList :=
{
    fail := @nil
}.
Proof.
  all: compute; reflexivity.
Defined.

Instance MonadAlt_List : MonadAlt MonadList :=
{
    choose := @app;
}.
Proof.
  all: intros.
    rewrite app_assoc. reflexivity.
    cbn. apply bind_List_app.
Defined.

Instance MonadNondet_List : MonadNondet MonadList :=
{
    instF := MonadFail_List;
    instA := MonadAlt_List;
}.
Proof.
  all: cbn; intros.
    reflexivity.
    rewrite app_nil_r. reflexivity.
Defined.

Arguments fail [M inst MonadFail A].
Arguments choose [M inst MonadAlt A] _ _.

Section S1.

Variable M : Type -> Type.
Variable inst : Monad M.

Fixpoint select
  {inst' : MonadNondet inst} {A : Type} (l : list A) : M (A * list A) :=
match l with
    | [] => fail
    | x :: xs => 
        choose (ret (x, xs)) $ do
          p <- select xs;
          let '(y, ys) := p in
            ret (y, x :: ys)
end.

Fixpoint perms' (n : nat)
  {inst' : MonadNondet inst} {A : Type} (l : list A) : M (list A) :=
match n, l with
    | 0, _ => fail
    | _, [] => ret []
    | S n', _ => do
        p <- select l;
        let '(h, t) := p in
        rest <- perms' n' t;
        ret (h :: rest)
end.

Definition perms 
  {inst' : MonadNondet inst} {A : Type} (l : list A) : M (list A) :=
    perms' (S (length l)) l.

End S1.

Compute select [1; 2; 3].

Compute perms [1; 2; 3].

(** ** 5. Exceptional computations *)

Section S2.

Variable M : Type -> Type.
Variable inst : Monad M.

(** [catch] and [fail] form a monoid. Pure computations need no handler. *)
Class MonadExcept
  (inst' : MonadFail inst) : Type :=
{
    catch : forall {A : Type}, M A -> M A -> M A;
    catch_fail_l :
      forall (A : Type) (x : M A),
        catch fail x = x;
    catch_fail_r :
      forall (A : Type) (x : M A),
        catch x fail = x;
    catch_assoc :
      forall (A : Type) (x y z : M A),
        catch (catch x y) z = catch x (catch y z);
    catch_ret :
      forall (A : Type) (x : A) (h : M A),
        catch (ret x) h = ret x;
}.

Goal
  forall (instF : MonadFail inst)
  (instE : MonadExcept instF) (A : Type) (f : A -> A) (x : M A) (h : M A),
    catch (ret f <*> x) h = ret f <*> catch x h.
Proof.
  intros.
Abort. (* TODO *)

Fixpoint product (l : list nat) : nat :=
match l with
    | [] => 1
    | h :: t => h * product t
end.

Lemma product_In_0 :
  forall l : list nat,
    In 0 l -> product l = 0.
Proof.
  induction l as [| h t]; cbn; destruct 1; subst.
    reflexivity.
    rewrite IHt; auto.
Qed.

Fixpoint has (n : nat) (l : list nat) : bool :=
match l with
    | [] => false
    | h :: t => beq_nat n h || has n t
end.

Lemma product_has_0 :
  forall l : list nat,
    has 0 l = true -> product l = 0.
Proof.
  induction l as [| h t]; cbn; intros.
    congruence.
    destruct h as [| h'].
      reflexivity.
      rewrite IHt; auto.
Qed.

Definition work
  {inst' : MonadFail inst} (l : list nat) : M nat :=
    if has 0 l then fail else ret (product l).

Definition fastprod
  {inst' : MonadFail inst} {inst'' : MonadExcept inst'}
    (l : list nat) : M nat := catch (work l) (ret 0).

Theorem fastprod_spec :
  forall (inst' : MonadFail inst) (inst'' : MonadExcept inst') (l : list nat),
    fastprod l = ret (product l).
Proof.
  unfold fastprod, work; intros.
  case_eq (has 0 l); intros.
    rewrite catch_fail_l, product_has_0; auto.
    rewrite catch_ret. reflexivity.
Qed.

(** wut *)

Definition next
  {inst' : MonadFail inst} (n : nat) (ml : M nat) : M nat :=
    if beq_nat 0 n then fail else fmap (mult n) ml.

Lemma work_foldr :
  forall (inst' : MonadFail inst),
    work = fold_right next (ret 1).
Proof.
  intros. ext l. induction l as [| h t]; cbn.
    reflexivity.
    unfold work in *. cbn. destruct h as [| h']; cbn.
      reflexivity.
      case_eq (has 0 t); intros.
        rewrite H in *. rewrite <- IHt. rewrite fmap_bind_ret.
          rewrite bind_fail_l'. reflexivity.
        rewrite H in *. rewrite <- IHt. rewrite fmap_ret. reflexivity.
Qed.

Fixpoint hasE
  {inst' : MonadFail inst} {inst'' : MonadExcept inst'}
  (n : nat) (l : list nat) : M unit :=
match l with
    | [] => ret tt
    | h :: t => if beq_nat n h then fail else hasE n t
end.

Definition fastprod'
  {inst' : MonadFail inst} {inst'' : MonadExcept inst'}
  (l : list nat) : M nat :=
    catch (hasE 0 l >> ret (product l)) (ret 0).

Theorem fastprod'_spec :
  forall (inst' : MonadFail inst) (inst'' : MonadExcept inst') (l : list nat),
    fastprod' l = ret (product l).
Proof.
  intros. unfold fastprod'.
  assert (forall n m : nat, catch (hasE 0 l >> ret n) (ret m) =
          if has 0 l then ret m else ret n).
    induction l as [| h t]; cbn in *; intros.
      unfold bind_. rewrite bind_ret_l, catch_ret. reflexivity.
      destruct h as [| h'].
        rewrite bind_fail_l, catch_fail_l. cbn. reflexivity.
        rewrite IHt. cbn. reflexivity.
    rewrite H. case_eq (has 0 l); intros.
      rewrite product_has_0; auto.
      reflexivity.
Qed.

End S2.

(** ** 6. Stateful computations *)

Arguments skip [M inst].

Class MonadState
  (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    get : M S;
    put : S -> M unit;
    put_put :
      forall s s' : S,
        put s >> put s' = put s';
    put_get :
      forall s : S,
        put s >> get = put s >> ret s;
    get_put :
      get >>= put = skip;
    get_get :
      forall (A : Type) (f : S -> S -> M A),
        get >>= (fun s : S => get >>= f s) =
        get >>= (fun s : S => f s s);
}.

(** ** 7. Combining effects *)

Class MonadStateNondet
  (S : Type) (M : Type -> Type) (inst : Monad M) : Type :=
{
    instS :> MonadState S inst;
    instN :> MonadNondet inst;
    seq_fail_r :
      forall (A B : Type) (x : M A),
        x >> fail = @fail M inst instN B;
    bind_choose_distr :
      forall (A B : Type) (f g : A -> M B) (ma : M A),
        ma >>= (fun x : A => choose (f x) (g x)) =
        choose (ma >>= f) (ma >>= g)
}.

Section S3.

Variable M : Type -> Type.
Variable inst : Monad M.

Lemma guard_seq_bind :
  forall (S : Type) (inst' : MonadStateNondet S inst) (A : Type)
  (b : bool) (ma : M A),
    guard b >> ma = ma >>= fun a : A => guard b >> ret a.
Proof.
  intros. unfold guard. destruct b.
    unfold skip, bind_. monad.
    rewrite bind_fail_l. rewrite <- (seq_fail_r _ _ ma).
      unfold bind_. f_equal. ext a.
      assert (H := bind_fail_l). unfold bind_ in H. rewrite H. reflexivity.
Qed.

End S3.

(** ** 8. Probabilistic computations *)

Section S4.

Axiom (Prob : Type).
Axiom p0 : Prob.
Axiom p1 : Prob.
Axiom neg : Prob -> Prob.
Axiom mul : Prob -> Prob -> Prob.

Class MonadProb_no_laws
  (M : Type -> Type) (inst : Monad M) : Type :=
{
    choice : forall {A : Type}, Prob -> M A -> M A -> M A;
}.

Notation "x <| p |> y" := (choice p x y)
  (left associativity, at level 5).

Class MonadProb
  (M : Type -> Type) (inst : Monad M) : Type :=
{
    instP :> MonadProb_no_laws inst;
    choice_p0 :
      forall (A : Type) (x y : M A),
        x <| p0 |> y = x;
    choice_p1 :
      forall (A : Type) (x y : M A),
        x <| p1 |> y = y;
    choice_qcomm :
      forall (A : Type) (x y : M A) (p : Prob),
        x <| p |> y = y <| neg p |> x;
    choice_idempotent :
      forall (A : Type) (x : M A) (p : Prob),
        x <| p |> x = x;
    choice_qassoc :
      forall (A : Type) (x y z : M A) (p q r s : Prob),
        p = mul r s -> neg s = mul (neg p) (neg q) ->
          x <| p |> (y <| q |> z) =
          (x <| r |> y) <| s |> z;
    bind_choice :
      forall (A B : Type) (p : Prob) (x y : M A) (f : A -> M B),
        (x <| p |> y) >>= f = (x >>= f) <| p |> (y >>= f);
    choice_bind :
      forall (A B : Type) (p : Prob) (ma : M A) (f g : A -> M B),
        ma >>= (fun x : A => (f x) <| p |> (g x)) =
        (ma >>= f) <| p |> (ma >>= g)
      
}.

End S4.