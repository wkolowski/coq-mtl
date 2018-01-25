Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Monad.
Require Import Control.MonadInst.
Require Import HSLib.Instances.All.
Require Import HSLib.InstancesT.AllT.

Require Import Ascii.
Require Import String.

Print Monad.

Definition Parser (A : Type) : Type :=
  StateT string list A.

(** *** 2.2 Primitive parsers *)

Definition fail {A : Type} : Parser A :=
  fun _ => [].

Definition item : Parser ascii :=
  fun input : string =>
  match input with
      | EmptyString => []
      | String c cs => ret (c, cs)
  end.

(** *** 2.3 Parser combinators *)

Definition seq
  {A B : Type} (pa : Parser A) (pb : Parser B) : Parser (A * B) :=
    pa >>= fun a => pb >>= fun b => ret (a, b).

Definition sat (p : ascii -> bool) : Parser ascii :=
  item >>= fun c : ascii => if p c then ret c else fail.

Require Import Bool.

Definition ascii_eqb (x y : ascii) : bool :=
  if ascii_dec x y then true else false.

Lemma ascii_eqb_spec :
  forall x y : ascii, reflect (x = y) (ascii_eqb x y).
Proof.
  intros. unfold ascii_eqb.
  destruct (ascii_dec x y); firstorder.
Qed.

Definition char (c : ascii) : Parser ascii :=
  sat (fun c' : ascii => ascii_eqb c c').

Open Scope char_scope.
Open Scope string_scope.

Require Import Arith.

Definition digit : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 48 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 57).

Definition lower : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 97 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 122).

Definition upper : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 65 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 90).

Open Scope list_scope.

(*Definition aplus {A : Type} (p1 p2 : Parser A) : Parser A :=
  fun input : string => (p1 input) ++ (p2 input).

Notation "x <|> y" := (aplus x y) (at level 42).*)

Definition letter : Parser ascii :=
  lower <|> upper.

Definition alnum : Parser ascii :=
  letter <|> digit.

(** All words of length less than or equal to n. *)
Fixpoint words (n : nat) : Parser string :=
match n with
    | 0 => ret ""
    | S n' => (String <$> letter <*> words n') <|> ret ""
end.

(** A word of any length. *)
Definition word : Parser string :=
  fun input : string => words (String.length input) input.

Arguments word _%string.

Compute word "dupa konia".

Fixpoint str (s : string) : Parser string :=
match s with
    | "" => ret ""
    | String c cs => String <$> char c <*> str cs
end.

Compute str "abc" "abcd".

Fixpoint many'
  {A : Type} (n : nat) (p : Parser A) : Parser (list A) :=
match n with
    | 0 => ret []
    | S n' => (cons <$> p <*> many' n' p) <|> ret []
end.

Arguments many' [A] _ _ _%string.

Open Scope char_scope.

Compute many' 5 letter "asdsd".

Definition many {A : Type} (p : Parser A) : Parser (list A) :=
  fun input : string => many' (String.length input) p input.

Arguments many {A} _ _%string.

Compute many digit "123".

Fixpoint toString (l : list ascii) : string :=
match l with
    | [] => ""
    | c :: cs => String c (toString cs)
end.

Definition word' : Parser string :=
  fmap toString (many letter).

Arguments word' _%string.

Compute word "abc".
Compute word' "abc".

Definition ident : Parser string := do
  c <- lower;
  cs <- fmap toString (many alnum);
  ret (String c cs).

Arguments ident _%string.

Compute ident "wut123".

Definition many1
  {A : Type} (p : Parser A) : Parser (list A) :=
    cons <$> p <*> (many p).

Arguments many1 [A] _ _%string.

Compute many1 (char "a") "aaab".

Fixpoint eval (cs : list ascii) : nat :=
match cs with
    | [] => 0
    | c :: cs' => nat_of_ascii c - 48 + 10 * eval cs'
end.

Definition parseNat : Parser nat :=
  fmap (fun l => eval (rev l)) (many1 digit).

Arguments parseNat _%string.

Compute parseNat "123".

Require Import ZArith.

Definition parseNeg : Parser nat := do
  char "-";;
  r <- many1 digit;
  ret $ eval (rev r).

Definition parseZ : Parser Z :=
  fmap Z_of_nat parseNat <|>
  fmap (fun n => Z.sub 0%Z (Z_of_nat n)) parseNeg.

Arguments parseZ _%string.

Compute parseZ "-12345".

Definition parseSign : Parser (Z -> Z) :=
  (char "-" >> ret (fun k => Z.sub 0%Z k)) <|>
  ret id.

Definition parsePositive : Parser positive :=
  parseNat >>= fun n : nat =>
  match n with
      | 0 => fail
      | _ => ret $ Pos.of_nat n
  end.

Definition parseSign' : Parser (Z -> Z) :=
  char "-" >> ret Z.opp <|> ret id.

Arguments parseSign' _%string.

Definition parseZ' : Parser Z := do
  sgn <- parseSign;
  n <- parseNat;
  ret $ sgn (Z_of_nat n).

Arguments parseZ' _%string.

Compute parseZ' "-12345".

Definition sepby1
  {A B : Type} (p : Parser A) (sep : Parser B)
  : Parser (list A) := do
    h <- p;
    t <- many (sep >> p);
    ret (h :: t).

Definition bracket {A B C : Type}
  (open : Parser A) (content : Parser B) (close : Parser C) : Parser B := do
    open;;
    res <- content;
    close;;
    ret res.

Definition ints : Parser (list Z) :=
  bracket (char "[") (sepby1 parseZ (char ",")) (char "]").

Arguments ints _%string.

Compute ints "[1,2,3,4,5,6,7,8]".

Definition sepby {A B : Type}
  (item : Parser A) (sep : Parser B) : Parser (list A) :=
    sepby1 item sep <|> ret [].

(**
    expr    ::= expr addop factor | factor
    addop   ::= + | -
    factor  ::= nat | ( expr )
*)

Fixpoint exprn (n : nat) : Parser Z :=
match n with
    | 0 => ret []
    | S n' =>
        let
          addop := char "+" >> ret Z.add <|>
                   char "-" >> ret Z.sub
        in let
          factor := parseZ <|>
                    bracket (char "(") (exprn n') (char ")")
        in
          liftA3 (fun x op y => op x y) (exprn n') addop factor <|>
          factor
end.

Definition expr : Parser Z :=
  fun input : string => exprn (String.length input) input.

Arguments expr _%string.

Compute expr "2+2".

Compute expr "0-5)".

Definition chainl1
  {A : Type} (obj : Parser A) (op : Parser (A -> A -> A)) : Parser A :=
  do
    h <- obj;
    t <- many $ liftA2 pair op obj;
    ret $ fold_left (fun x '(f, y) => f x y) t h.

Definition parseNat_chainl : Parser nat :=
  let op m n := 10 * m + n in
    chainl1 (fmap (fun d => nat_of_ascii d - nat_of_ascii "0") digit) (ret op).

Arguments parseNat_chainl _%string.

Compute parseNat_chainl "211".

Fixpoint chainr1_aux
  {A : Type} (arg : Parser A) (op : Parser (A -> A -> A)) (n : nat)
  : Parser A :=
match n with
    | 0 => fail
    | S n' => op <*> arg <*> chainr1_aux arg op n' <|> arg
end.

Definition chainr1
  {A : Type} (arg : Parser A) (op : Parser (A -> A -> A)) : Parser A :=
    fun input : string => chainr1_aux arg op (String.length input) input.

Arguments chainr1 {A} _ _ _%string.

Definition parseNat_chainr : Parser nat :=
  let op m n := m + 10 * n in
    chainr1 (fmap (fun d => nat_of_ascii d - nat_of_ascii "0") digit) (ret op).

Arguments parseNat_chainr _%string.

Compute parseNat_chainr "211".

Fixpoint exprn'' (n : nat) : Parser Z :=
match n with
    | 0 => ret [] (* 0%Z *)
    | S n' =>
        let
          op := char "+" >> ret Z.add <|>
                char "-" >> ret Z.sub
        in let
          factor := parseZ <|> bracket (char "(") (exprn'' n') (char ")")
        in
          chainl1 factor op
end.

Definition expr'' : Parser Z :=
  fun input : string => exprn'' (String.length input) input.

Arguments expr'' _%string.

Compute expr'' "3-2"%string.

Definition ops
  {A B : Type} (start : Parser A * B) (l : list (Parser A * B)) : Parser B :=
match l with
    | [] => let '(p, op) := start in p >> ret op
    | h :: t =>
        let '(p, op) := start in
          fold_right aplus (p >> ret op)
            (map (fun '(p, op) => p >> ret op) l)
end.

Fixpoint exprn3 (n : nat) : Parser Z :=
match n with
    | 0 => fail (* ret [] *) (* 0%Z *)
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

Compute expr'' "1-(2-(3-4)-5)"%string.

(* TODO: chainl1 alternative *)

Fixpoint exprn4 (n : nat) : Parser Z :=
match n with
    | 0 => fail
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

Arguments expr4 _%string.

Compute expr4 "(1-2)^3".

Definition chainl
  {A : Type} (p : Parser A) (op : Parser (A -> A -> A)) (default : A)
    : Parser A := chainl1 p op <|> ret default.

Definition chainr
  {A : Type} (p : Parser A) (op : Parser (A -> A -> A)) (default : A)
    : Parser A := chainr1 p op <|> ret default.

Definition first
  {A : Type} (p : Parser A) : Parser A :=
    fun input : string =>
match p input with
    | [] => []
    | h :: _ => [h]
end.

Definition aplus_det
  {A : Type} (p q : Parser A) : Parser A :=
    first (p <|> q).

Notation "p +++ q" := (aplus_det p q) (at level 42).

Theorem aplus_det_spec :
  forall (A : Type) (p q : Parser A),
    p <|> q = (fun _ => []) \/
    (exists x : A * string, p <|> q = fun _ => [x]) ->
      p +++ q = p <|> q.
Proof.
  intros. extensionality input. unfold aplus_det, first.
  (* BEWARE: ]] gives an error *)
  destruct H as [H | [x H] ]; rewrite H; reflexivity.
Qed.

Definition isSpace (c : ascii) : bool :=
  leb (nat_of_ascii c) 32.

Definition spaces : Parser unit :=
  many1 (sat isSpace) >> ret tt.

Definition comment : Parser unit :=
  first
    (str "--" >> many (sat (fun c => negb (ascii_eqb c "013"))) >> ret tt).

Arguments comment _%string.

Compute comment "-- haskellowy komentarz polityczny".

Definition junk : Parser unit :=
  many (spaces +++ comment) >> ret tt.

Definition parse {A : Type} (p : Parser A) : Parser A :=
  junk >> p.

Definition token {A : Type} (p : Parser A) : Parser A :=
  do
    x <- p;
    junk;;
    ret x.

Definition natural : Parser nat :=
  token parseNat.

Definition integer : Parser Z :=
  token parseZ.

Definition symbol (s : string) : Parser string :=
  token (str s).

Definition in_decb {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A)
    : bool := if in_dec eq_dec x l then true else false.

Definition identifier (keywords : list string) : Parser string :=
  do
    id <- token ident;
    if in_decb string_dec id keywords then fail else ret id.

Arguments spaces _%string.
Arguments comment _%string.
Arguments symbol _%string.
Arguments natural _%string.
Arguments identifier _%string.

Compute natural "123"%string.

Module Q.

Definition nonzeroDigit : Parser ascii :=
  sat (fun c : ascii => leb 49 (nat_of_ascii c) && leb (nat_of_ascii c) 58).

Require Import QArith.

Definition parseQ : Parser Q := do
  a <- parseZ;
  char "/";;
  b <- parsePositive;
  ret (a # b).

Arguments parseQ _%string.

Compute parseQ "1/5".

End Q.

Inductive Expr : Type :=
    | App : Expr -> Expr -> Expr
    | Lam : string -> Expr -> Expr
    | Let : string -> Expr -> Expr -> Expr
    | Var : string -> Expr.

(* Lambda calculus parser for Coq-like syntax. *)
Time Fixpoint parseExprn (n : nat) : Parser Expr :=
match n with
    | 0 => fail
    | S n' =>
        let
          id := identifier ["let"; "fun"; "in"]%string
        in let
          app := do
            token $ char "(";;
            e1 <- parseExprn n';
            e2 <- parseExprn n';
            token $ char ")";;
            ret $ App e1 e2
        in let
          lam := do
            token $ str "fun";;
            var <- id;
            token $ str "=>";;
            body <- parseExprn n';
            ret $ Lam var body
        in let
          parseLet := do
            token $ str "let";;
            var <- id;
            token $ str ":=";;
            body <- parseExprn n';
            token $ str "in";;
            let_body <- parseExprn n';
            ret $ Let var body let_body
        in let
          var := fmap Var id
        in
          app +++ lam +++ parseLet +++ var
end.

Definition parseExpr : Parser Expr :=
  fun input : string => parseExprn (String.length input) input.

Arguments parseExpr _%string.

Time Compute parseExpr "(x x)"%string.
Time Compute parseExpr "fun f => fun x => (f x)".
Time Compute parseExpr "let x := (x x) in x".

(** Parser for lambda calculus with Haskell-like syntax taken directly
    from the paper. *)
Time Fixpoint parseExprn' (n : nat) : Parser Expr :=
match n with
    | 0 => fail
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
            ret $ Let x e e'
        in let
          lam := do
            symbol "\";;
            x <- variable;
            symbol "->";;
            e <- parseExprn' n';
            ret $ Lam x e
        in let
          atom := token (lam +++ local +++ var +++ paren)
        in
          chainl1 atom (ret App)
end.

Definition parseExpr' : Parser Expr :=
  fun input : string => parseExprn' (String.length input) input.

Arguments parseExpr' _%string.

Time Compute parseExpr' "(x x)".
Time Compute parseExpr' "\f -> \x -> (f x)".
Time Compute parseExpr' "let x = (x x) in x".