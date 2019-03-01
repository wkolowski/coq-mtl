Require Export Bool.
Require Export Arith.

Require Export Ascii.
Require Export String.

Require Import Control.All.

Require Export Control.Monad.ListInst.
Require Export Control.Monad.Trans.StateT.

(** A parser is just a nondeterministic monad with state. *)
Definition Parser (A : Type) : Type :=
  StateT string list A.

(** Parse a single character and return the rest of the input as the
    current state. *)
Definition item : Parser ascii :=
  fun input : string =>
  match input with
      | EmptyString => []
      | String c cs => pure (c, cs)
  end.

(** Parse a character that satisfies a boolean predicate. *)
Definition sat (p : ascii -> bool) : Parser ascii :=
  item >>= fun c : ascii => if p c then pure c else aempty.

(** Decide equality of two characters. *)
Definition ascii_eqb (x y : ascii) : bool :=
  if ascii_dec x y then true else false.

(** Parsers for single characters of the given kind: any character, digit,
    nonzero digit, lowercase ascii, uppercase ascii, any lowercase or
    uppercase letter, any letter or digit. *)
Definition char (c : ascii) : Parser ascii :=
  sat (fun c' : ascii => ascii_eqb c c').

Definition digit : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 48 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 57).

Definition nonzeroDigit : Parser ascii :=
  sat (fun c : ascii => leb 49 (nat_of_ascii c) && leb (nat_of_ascii c) 58).

Definition lower : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 97 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 122).

Definition upper : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 65 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 90).

Definition letter : Parser ascii :=
  lower <|> upper.

Definition alnum : Parser ascii :=
  letter <|> digit.

(** We're done with parsing single characters so that we can now proceed to
    work with strings in their scope. *)
Open Scope string_scope.

(** Parse a word of length less than or equal to [n]. *)
Fixpoint words (n : nat) : Parser string :=
match n with
    | 0 => pure ""
    | S n' => (String <$> letter <*> words n') <|> pure ""
end.

(** Parse a word of any length. Note that this may in theory not work,
    because the recursion depth required to parse the input may be greater
    than the input's length. *)
Definition word : Parser string :=
  fun input : string => words (String.length input) input.

(** Parse precisely the given string. *)
Fixpoint str (s : string) : Parser string :=
match s with
    | "" => pure ""
    | String c cs => String <$> char c <*> str cs
end.

(** Run the parser [p] zero or more times. Fail if the input is longer than
    [n] characters. *)
Fixpoint many'
  {A : Type} (n : nat) (p : Parser A) : Parser (list A) :=
match n with
    | 0 => pure []
    | S n' => (cons <$> p <*> many' n' p) <|> pure []
end.

(** Run [p] zero or more times. The same remark as for [word] applies. *)
Definition many {A : Type} (p : Parser A) : Parser (list A) :=
  fun input : string => many' (String.length input) p input.

Fixpoint toString (l : list ascii) : string :=
match l with
    | [] => ""
    | c :: cs => String c (toString cs)
end.

(** An alternate definition of the parser for words. Note that it can still
    fail if the recursion depth required to successfuly parse is greater
    than the input's length. *)
Definition word' : Parser string :=
  fmap toString (many letter).

(** Parse an identifier, which is defined as a lowercase letter followed
    by any number of alphanumeric characters. *)
Definition ident : Parser string := do
  c <- lower;
  cs <- fmap toString (many alnum);
  pure (String c cs).

(** Run a parser one or more times. *)
Definition many1
  {A : Type} (p : Parser A) : Parser (list A) :=
    cons <$> p <*> (many p).

Fixpoint eval (cs : list ascii) : nat :=
match cs with
    | [] => 0
    | c :: cs' => nat_of_ascii c - 48 + 10 * eval cs'
end.

(** Parse a natural number written in decimal. *)
Definition parseNat : Parser nat :=
  fmap (fun l => eval (rev l)) (many1 digit).

Require Export ZArith.

(** Parse a natural number preceded by the minus sign. *)
Definition parseNeg : Parser nat := do
  char "-";;
  r <- many1 digit;
  pure $ eval (rev r).

(** Parse an integer written in decimal with a potential minus sign at the
    beginnig. *)
Definition parseZ : Parser Z :=
  fmap Z_of_nat parseNat <|>
  fmap (fun n => Z.sub 0%Z (Z_of_nat n)) parseNeg.

(** Try to parse a single character and return a function corresponding to it:
    negation in case if the character is "-" or identity otherwise. *)
Definition parseSign : Parser (Z -> Z) :=
  char "-" >> pure Z.opp <|> pure id.

(** Parse a natural number written in decimal that is not zero. *)
Definition parsePositive : Parser positive :=
  parseNat >>= fun n : nat =>
  match n with
      | 0 => aempty
      | _ => pure $ Pos.of_nat n
  end.

(** An alternative way to parse an integer written in decimal. *)
Definition parseZ' : Parser Z := do
  sgn <- parseSign;
  n <- parseNat;
  pure $ sgn (Z_of_nat n).

(** Parse a sequence of [p]'s separated by the separator [sep] like this:
    p sep p sep p ... sep p. There has to be at least one [p]. *)
Definition sepby1
  {A B : Type} (p : Parser A) (sep : Parser B)
  : Parser (list A) := do
    h <- p;
    t <- many (sep >> p);
    pure (h :: t).

(** Parse [content] enclosed in a left and a right "bracket" (which can be
    anything, not only "[" or "]"). *)
Definition bracket {A B C : Type}
  (open : Parser A) (content : Parser B) (close : Parser C) : Parser B := do
    open;;
    res <- content;
    close;;
    pure res.

(** Parse a list of integers (written in decimal) that is surrounded by
    brackets ("[" and "]") and entries are separated with commas. *)
Definition ints : Parser (list Z) :=
  bracket (char "[") (sepby1 parseZ (char ",")) (char "]").

(** Like [sepby1], but possibly empty. *)
Definition sepby {A B : Type}
  (item : Parser A) (sep : Parser B) : Parser (list A) :=
    sepby1 item sep <|> pure [].

(** Parse a sequence of things separated by meaningful separators that
    are binary operators. *)
Definition chainl1
  {A : Type} (obj : Parser A) (op : Parser (A -> A -> A)) : Parser A :=
  do
    h <- obj;
    t <- many $ liftA2 pair op obj;
    pure $ fold_left (fun x '(f, y) => f x y) t h.

Definition parseNat_chainl : Parser nat :=
  let op m n := 10 * m + n in
    chainl1 (fmap (fun d => nat_of_ascii d - nat_of_ascii "0") digit)
            (pure op).

Fixpoint chainr1_aux
  {A : Type} (arg : Parser A) (op : Parser (A -> A -> A)) (n : nat)
  : Parser A :=
match n with
    | 0 => aempty
    | S n' => op <*> arg <*> chainr1_aux arg op n' <|> arg
end.

(** Like [chainl1], but right-associative. *)
Definition chainr1
  {A : Type} (arg : Parser A) (op : Parser (A -> A -> A)) : Parser A :=
    fun input : string => chainr1_aux arg op (String.length input) input.

Definition parseNat_chainr : Parser nat :=
  let op m n := m + 10 * n in
    chainr1 (fmap (fun d => nat_of_ascii d - nat_of_ascii "0") digit)
            (pure op).

(** Parse all matching things from a nonempty list and interpret them
    accordingly. *)
Definition ops
  {A B : Type} (start : Parser A * B) (l : list (Parser A * B)) : Parser B :=
match l with
    | [] => let '(p, op) := start in p >> pure op
    | h :: t =>
        let '(p, op) := start in
          fold_right aplus (p >> pure op)
            (map (fun '(p, op) => p >> pure op) l)
end.

(** Like [chainl1], but with a default value. *)
Definition chainl
  {A : Type} (p : Parser A) (op : Parser (A -> A -> A)) (default : A)
    : Parser A := chainl1 p op <|> pure default.

(** Like [chain1], but with a default value. *)
Definition chainr
  {A : Type} (p : Parser A) (op : Parser (A -> A -> A)) (default : A)
    : Parser A := chainr1 p op <|> pure default.

(** Throw away all matches besides the first one. *)
Definition first
  {A : Type} (p : Parser A) : Parser A :=
    fun input : string =>
match p input with
    | [] => []
    | h :: _ => [h]
end.

(** A deterministic version of [aplus]. *)
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
  destruct H as [H | [x H]]; rewrite H; reflexivity.
Qed.

Definition isSpace (c : ascii) : bool :=
  leb (nat_of_ascii c) 32.

(** Throw away at least one space. Note that it is just space, not any
    whitespace. *)
Definition spaces : Parser unit :=
  many1 (sat isSpace) >> pure tt.

(** Deterministically parse a Haskell-style comment starting with "--" and
    ending with a newline character. *)
Definition comment : Parser unit :=
  first
    (str "--" >> many (sat (fun c => negb (ascii_eqb c "013"))) >> pure tt).

(** Throw away spaes and Haskell-style comments. *)
Definition junk : Parser unit :=
  many (spaces +++ comment) >> pure tt.

(** Throw away spaces and commes and then start parsing the meaningful part
    of the input. *)
Definition parse {A : Type} (p : Parser A) : Parser A :=
  junk >> p.

(** Parse meaningful stuff at the beginning of the input and then throw
    away spaces and comments. *)
Definition token {A : Type} (p : Parser A) : Parser A :=
  do
    x <- p;
    junk;;
    pure x.

(** Parse the desired thing and then remove spaces and comments from the
    end. *)
Definition natural : Parser nat :=
  token parseNat.

Definition integer : Parser Z :=
  token parseZ.

Definition symbol (s : string) : Parser string :=
  token (str s).

Definition in_decb {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A)
    : bool := if in_dec eq_dec x l then true else false.

(** Parse an identifier. An identifier here is any string that doesn't
    belong to the given list of forbidden keywords. *)
Definition identifier (keywords : list string) : Parser string :=
  do
    id <- token ident;
    if in_decb string_dec id keywords
    then aempty
    else pure id.

Require Import QArith.

(** Parse a rational number. *)
Definition parseQ : Parser Q := do
  a <- parseZ;
  char "/";;
  b <- parsePositive;
  pure (a # b).

Compute str "abc" "abcd".
Compute word "dupa konia".
Compute many' 5 letter "asdsd".
Compute many digit "123".
Compute word' "abc".
Compute word "abc".
Compute ident "varname".
Compute many1 (char "a") "aaab".
Compute parseNat "123".
Compute parseZ "-12345".
Compute parseZ' "-12345".
Compute ints "[1,2,3,4,5,6,7,8]".
Compute parseNat_chainl "211".
Compute parseNat_chainr "211".
Compute natural "123".
Compute parseQ "1/5".
Compute comment "-- haskellowy komentarz polityczny".