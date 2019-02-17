
Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (F_inst : Functor F)
  (pure : forall A : Type, A -> F A).

Inductive type : Type :=
    | TVar : Type -> type
    | TArr : type -> type -> type
    | TF : type -> type.

Fixpoint typeDenote (t : type) : Type :=
match t with
    | TVar A => A
    | TArr t1 t2 => typeDenote t1 -> typeDenote t2
    | TF t => F (typeDenote t)
end.

Inductive Exp : type -> Type :=
    | Var : forall A : Type, A -> Exp (TVar A)
    | Id : forall A : type, Exp (TArr A A)
    | Comp :
        forall A B C : type,
          Exp (TArr A B) -> Exp (TArr B C) -> Exp (TArr A C)
    | App : forall A B : type, Exp (TArr A B) -> Exp A -> Exp B
    | Fmap : forall A B : type, Exp (TArr A B) -> Exp (TArr (TF A) (TF B)).

Arguments Var {A}.
Arguments Id {A}.
Arguments Comp {A B C}.
Arguments App {A B}.
Arguments Fmap {A B}.

Fixpoint denote {A : type} (t : Exp A) : typeDenote A :=
match t with
    | Var x => x
    | Id => id
    | Comp f g => denote f .> denote g
    | App f x => denote f (denote x)
    | Fmap f => fmap (denote f)
end.

(*
Eval cbn in denote (App (Fmap (Var (plus 2))) (Var (pure _ 42))).
*)

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Definition simplify {A : type} (e : Exp A) : Exp A.
Proof.
  dependent induction e.
    exact (Var a).
    exact Id.
    dependent destruction IHe1.
      exact IHe2.
      exact (Comp (Comp IHe1_1 IHe1_2) IHe2).
      exact (Comp (App IHe1_1 IHe1_2) IHe2).
      exact (Comp (Fmap IHe1) IHe2).
(*      1-3: exact (Comp IHe1 IHe2).*)
    inversion IHe1; subst.
      exact e2.
      1-3: exact (App IHe1 IHe2).
    exact (Fmap IHe).
Defined.

Lemma denote_simplify :
  forall (t : type) (e : Exp t),
    denote (simplify e) = denote e.
Proof.
  dependent induction e.
    cbn. reflexivity.
    cbn. reflexivity. cbn. compute.
    (*cbn.*)
Abort.
Print Exp.
Definition simplify' {A : type} : Exp A -> Exp A.
revert A.
(*
refine (
  fix simplify {A : type} (e : Exp A) : Exp A :=
match e as e' in Exp t return (JMeq e e' -> Exp t) with
    | Var x => fun _ => Var x
    | Id => fun _ => Id
    | Comp e1 e2 => fun _ => (* TODO *)
        match simplify e1 as e1' in Exp t
        return (JMeq (simplify e1) e1' -> Exp t) with
            
            | _ => fun _ => _
        end JMeq_refl
    | App e1 e2 => fun _ => App (simplify e1) (simplify e2)
    | Fmap e => fun _ => Fmap (simplify e)
end (JMeq_refl)
).
*)
Abort.
(*
match e as e' return (e = e' -> Exp A) with
    | @Comp t1 t2 t3 e1 e2 => fun _ => Comp e1 e2 (*
      let
        rt {A : type} (e : Exp A) :=
        match e with
            | @Id t => Exp (TArr t t3)
            | _ => Exp (TArr t1 t3)
        end
      in
        match e1 return rt e1 with
            | Id => e2
            | _ => _
        end*)
    | _ => fun _ => e
end (eq_refl e)).
*)
(*
Class Reify {A : Type} (x : A) : Type :=
{
    reify : Exp A;
    denote_reify : denote reify = x
}.
Arguments reify {A} _ {Reify}.
Instance ReifyApp
  {A B C : Type} {f : A -> B} {x : A}
  (Rf : Reify f) (Rx : Reify x) : Reify (f x) | 0 :=
{
    reify := App (reify f) (reify x)
}.
Proof.
  cbn. rewrite 2!denote_reify. reflexivity.
Defined.
Instance ReifyFmap
  {A B : Type} (f : A -> B) (Rf : Reify f) : Reify (fmap f) | 0 :=
{
    reify := Fmap (reify f)
}.
Proof.
  cbn. rewrite denote_reify. reflexivity.
Defined.
Instance ReifyVar {A : Type} (x : A) : Reify x | 100 :=
{
    reify := Var x
}.
Proof.
  cbn. reflexivity.
Defined.
Eval cbn in reify f.
Eval cbn in reify x.
Eval cbn in reify (fmap f).
Eval cbn in reify (f x).
Check reify (f x).
*)

Variables
  (A B C : Type)
  (f : A -> A)
  (x y : A).

Print Exp.

Ltac reify e :=
match e with
    | id => constr:(Id)
    | ?f .> ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | compose ?f ?g =>
        let f' := reify f in
        let g' := reify g in constr:(Comp f' g')
    | ?f ?x =>
        let f' := reify f in
        let x' := reify x in constr:(App f' x')
    | fmap ?f => idtac f;
        let f' := reify f in constr:(Fmap f')
    | ?x => constr:(Var x)
(*    | _ => idtac e*)
end.

Goal 5 = 5.
Proof.
(*
  match constr:(fmap (plu
*)
  let x := reify constr:(f x) in pose x.
  let x := reify constr:(f .> f) in pose x.
Abort.

