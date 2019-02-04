Require Export HSLib.Control.Alternative.
Require Export HSLib.Control.Monad.
Require Export HSLib.Control.Monad.MonadPlus.

Require Export HSLib.Control.Monad.All.

Require Import Arith.

Fixpoint aux (n k : nat) : list nat :=
match n with
    | 0 => [k]
    | S n' => k :: aux n' (S k)
end.

Definition I (a b : nat) : list nat := aux (b - a) a.

(** Tests for [Alternative] and [MonadPlus]. *)
Compute do
  a <- I 1 25;
  b <- I 1 25;
  c <- I 1 25;
  guard (beq_nat (a * a + b * b) (c * c));;
  pure (a, b, c).

(*
Check mfilter (fun _ => true) (I 1 10).
Eval compute in mfilter (fun _ => false) (Some 42).
*)

Compute zipWithA
  (fun _ _ => [true; false]) [1; 2; 3] [4; 5; 6; 7].

(** Tests for [Foldable]. *)
Require Import HSLib.Control.Foldable.

Eval compute in isEmpty (None).
Eval compute in size (Some 42).
Eval compute in toListF (Some 5).
Eval compute in elem beq_nat 2 (Some 2).
Eval compute in maxF (Some 42).

Eval compute in size (inr 5).
Eval compute in maxF [1; 2; 3].
Eval compute in findFirst (beq_nat 42) [1; 3; 5; 7; 11; 42].
Eval compute in count (leb 10) [1; 3; 5; 7; 11; 42].

(** Tests for [Parser]. *)
Require Import HSLib.Parser.GeneralParser.
Require Import ZArith.
Require Import String.

Open Scope string_scope.

(**
    expr    ::= expr addop factor | factor
    addop   ::= + | -
    factor  ::= nat | ( expr )
*)

Time Fixpoint exprn (n : nat) : Parser Z :=
match n with
    | 0 => aempty
    | S n' =>
        let
          addop := char "+" >> pure Z.add <|>
                   char "-" >> pure Z.sub
        in let
          factor := parseZ <|>
                    bracket (char "(") (exprn n') (char ")")
        in
          liftA3 (fun x op y => op x y) (exprn n') addop factor <|>
          factor
end.

Definition expr : Parser Z :=
  fun input : string => exprn (String.length input) input.

Compute expr "2+2".

Compute expr "0-5)".

(** The same grammar as above. *)
Time Fixpoint exprn2 (n : nat) : Parser Z :=
match n with
    | 0 => aempty
    | S n' =>
        let
          op := char "+" >> pure Z.add <|>
                char "-" >> pure Z.sub
        in let
          factor := parseZ <|> bracket (char "(") (exprn2 n') (char ")")
        in
          chainl1 factor op
end.

Definition expr2 : Parser Z :=
  fun input : string => exprn2 (String.length input) input.

Compute expr2 "3-2"%string.

(** Still the same grammar. *)
Time Fixpoint exprn3 (n : nat) : Parser Z :=
match n with
    | 0 => aempty
    | S n' =>
        let
          op := ops (char "+", Z.add) [(char "-", Z.sub)]
        in let
          factor := parseZ <|> bracket (char "(") (exprn3 n') (char ")")
        in
          chainl1 factor op
end.

Definition expr3 : Parser Z :=
  fun input : string => exprn3 (String.length input) input.

Compute expr3 "1-(2-(3-4)-5)"%string.

(** Nearly as before, but augmented with "^" for exponentiation. *)
Fixpoint exprn4 (n : nat) : Parser Z :=
match n with
    | 0 => aempty
    | S n' =>
        let
          addop := ops (char "+", Z.add) [(char "-", Z.sub)]
        in let
          expop := ops (char "^", Z.pow) []
        in let
          factor := parseZ <|> bracket (char "(") (exprn4 n') (char ")")
        in let
          term := chainr1 factor expop
        in
          chainl1 term addop
end.

Definition expr4 : Parser Z :=
  fun input : string => exprn4 (String.length input) input.

Compute expr4 "(1-2)^3".

Inductive Expr : Type :=
    | App : Expr -> Expr -> Expr
    | Lam : string -> Expr -> Expr
    | Let : string -> Expr -> Expr -> Expr
    | Var : string -> Expr.

(** Parser for lambda calculus with let using Coq-like syntax. *)
Time Fixpoint parseExprn (n : nat) : Parser Expr :=
match n with
    | 0 => aempty
    | S n' =>
        let
          id := identifier ["let"; "fun"; "in"]%string
        in let
          app := do
            token $ char "(";;
            e1 <- parseExprn n';
            e2 <- parseExprn n';
            token $ char ")";;
            pure $ App e1 e2
        in let
          lam := do
            token $ str "fun";;
            var <- id;
            token $ str "=>";;
            body <- parseExprn n';
            pure $ Lam var body
        in let
          parseLet := do
            token $ str "let";;
            var <- id;
            token $ str ":=";;
            body <- parseExprn n';
            token $ str "in";;
            let_body <- parseExprn n';
            pure $ Let var body let_body
        in let
          var := fmap Var id
        in
          app +++ lam +++ parseLet +++ var
end.

Definition parseExpr : Parser Expr :=
  fun input : string => parseExprn (String.length input) input.

Time Compute parseExpr "(x x)".
Time Compute parseExpr "fun f => fun x => (f x)".
Time Compute parseExpr "let x := (x x) in x".

(** Parser for lambda calculus with let using Haskell-like syntax. Taken
    directly from the paper. *)
Time Fixpoint parseExprn' (n : nat) : Parser Expr :=
match n with
    | 0 => aempty
    | S n' =>
        let
          variable := identifier ["let"; "in"]%string
        in let
          paren := bracket (char "(") (parseExprn' n') (char ")")
        in let
          var := fmap Var variable
        in let
          local := do
            symbol "let";;
            x <- variable;
            symbol "=";;
            e <- parseExprn' n';
            symbol "in";;
            e' <- parseExprn' n';
            pure $ Let x e e'
        in let
          lam := do
            symbol "\";;
            x <- variable;
            symbol "->";;
            e <- parseExprn' n';
            pure $ Lam x e
        in let
          atom := token (lam +++ local +++ var +++ paren)
        in
          chainl1 atom (pure App)
end.

Definition parseExpr' : Parser Expr :=
  fun input : string => parseExprn' (String.length input) input.

Time Compute parseExpr' "(x x)".
Time Compute parseExpr' "\f -> \x -> (f x)".
Time Compute parseExpr' "let x = (x x) in x".