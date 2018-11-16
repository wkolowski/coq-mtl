Require Export Control.Functor.

Variables
  (F : Type -> Type)
  (F_inst : Functor F)
  (pure : forall A : Type, A -> F A).

Inductive Exp : Type :=
    | Var : forall A : Type, A -> Exp
    | Id : Exp
    | Comp : Exp -> Exp -> Exp
    | App : Exp -> Exp -> Exp
    | Fmap : Exp -> Exp.

Arguments Var {A}.

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

(*
Fixpoint infer (e : Exp) : type :=
match e with
    | @Var A _ => TVar A
    | 
end.
*)

Inductive hasType : Exp -> type -> Type :=
    | ht_Var :
        forall (A : Type) (x : A), hasType (Var x) (TVar A)
    | ht_Id :
        forall A : type, hasType Id (TArr A A)
    | ht_Comp :
        forall (A B C : type) (e1 e2 : Exp),
          hasType e1 (TArr A B) -> hasType e2 (TArr B C) ->
            hasType (Comp e1 e2) (TArr A C)
    | ht_App :
        forall (A B : type) (e1 e2 : Exp),
          hasType e1 (TArr A B) -> hasType e2 A ->
            hasType (App e1 e2) B
    | ht_Fmap :
        forall (A B : type) (e : Exp),
          hasType e (TArr A B) -> hasType (Fmap e) (TArr (TF A) (TF B)).

Hint Constructors hasType.

Function denote {e : Exp} {t : type} (ht : hasType e t) : typeDenote t :=
match ht with
    | ht_Var _ x => x
    | ht_Id _ => id
    | ht_Comp _ _ _ _ _ e1 e2 => denote e1 .> denote e2
    | ht_App _ _ _ _ e1 e2 => denote e1 (denote e2)
    | ht_Fmap _ _ _ e => fmap (denote e)
end.

Lemma denote_eq {e : Exp} {t : type} (ht : hasType e t) :
  denote ht =
  match ht with
      | ht_Var _ x => x
      | ht_Id _ => id
      | ht_Comp _ _ _ _ _ e1 e2 => denote e1 .> denote e2
      | ht_App _ _ _ _ e1 e2 => denote e1 (denote e2)
      | ht_Fmap _ _ _ e => fmap (denote e)
  end.
Proof.
  destruct ht; cbn; reflexivity.
Defined.

Require Import Recdef.

Function simplify (e : Exp) : Exp :=
match e with
    | Var x => Var x
    | Id => Id
    | Comp e1 e2 =>
        match simplify e1, simplify e2 with
            | Id, e2' => e2'
            | e1', Id => e1'
            | e1', e2' => Comp e1' e2'
        end
    | App e1 e2 =>
        match simplify e1 with
            | Id => simplify e2
            | e1' => App e1' (simplify e2)
        end
    | Fmap e' =>
        match simplify e' with
            | Id => Id
            | Comp e1 e2 => Comp (Fmap e1) (Fmap e2)
            | e'' => Fmap e''
        end
end.

Lemma hasType_simplify :
  forall {e : Exp} {t : type},
    hasType e t -> hasType (simplify e) t.
Proof.
  induction 1; cbn; eauto.
    inv IHX1; inv IHX2; eauto.
    inv IHX1; inv IHX2; eauto.
    inv IHX; eauto.
Defined.

Lemma denote_simplify :
  forall {e : Exp} {t : type} (ht : hasType e t),
    denote (hasType_simplify ht) = denote ht.
Proof.
  induction ht.
    reflexivity.
    reflexivity.
Abort.