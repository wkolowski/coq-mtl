(** * Monadic Parser Combinators *)

(** This file is a Coq translation of code taken from the paper "Monadic
    Parser Combinators" by Graham Hutton and Erik Meijer. *)

Require Import Ascii.
Require Import String.

Require Import List.
Import ListNotations.

(** ** 1 Introduction *)

(** ** 2 Combinator parsers *)

(** *** 2.1 The type of parsers *)

Definition Parser (A : Type) : Type := string -> list (A * string).

(** *** 2.2 Primitive parsers *)

Definition result {A : Type} (x : A) : Parser A :=
  fun input : string => [(x, input)].

Definition zero {A : Type} : Parser A :=
  fun _ => [].

Definition item {A : Type} : Parser ascii :=
  fun input : string =>
  match input with
      | EmptyString => []
      | String c cs => [(c, cs)]
  end.

(** *** 2.3 Parser combinators *)

Fixpoint join {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | l :: ls => l ++ join ls
end.

Definition bind
  {A B : Type} (p : Parser A) (f : A -> Parser B) : Parser B :=
  fun input : string =>
    join (map (fun x : A * string =>
      let '(v, input') := x in f v input') (p input)).

Definition seq
  {A B : Type} (pa : Parser A) (pb : Parser B) : Parser (A * B) :=
    bind pa (fun a : A =>
    bind pb (fun b : B =>
      result (a, b))).

Definition sat (p : ascii -> bool) : Parser ascii :=
  bind (@item ascii) (fun c : ascii =>
    if p c then result c else zero).

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

Compute nat_of_ascii "A".
Compute nat_of_ascii "Z".

Definition upper : Parser ascii :=
  sat (fun c : ascii =>
    Nat.leb 65 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 90).

Compute bind lower (fun x =>
        bind lower (fun y =>
          result (String x (String y EmptyString)))) "hello".

Open Scope list_scope.

Definition plus {A : Type} (p1 p2 : Parser A) : Parser A :=
  fun input : string => (p1 input) ++ (p2 input).

Definition letter : Parser ascii :=
  plus lower upper.

Definition alphanum : Parser ascii :=
  plus letter digit.

(** All words of length less than or equal to n. *)
Fixpoint words (n : nat) : Parser string :=
match n with
    | 0 => result ""
    | S n' => plus
                (bind letter (fun c =>
                 bind (words n') (fun cs =>
                   result (String c cs))))
                (result "")
end.

(** A word of any length. *)
Definition word : Parser string :=
  fun input : string => words (String.length input) input.

(** ** 3 Parsers and monads *)

(** *** 3.1 The parser monad *)

(* TODO *)

(** *** 3.2 Monad comprehension syntax *)

Fixpoint str (s : string) : Parser string :=
(*  fun input : string =>*)
match s with
    | "" => result ""
    | String c cs =>
        bind (char c) (fun _ => bind (str cs) (fun _ => result (String c cs)))
end.

Compute str "abc" "abcd".

(** ** 4 Combinators for repetition *)

(** *** 4.1 Simple repetition *)

Fixpoint many' {A : Type} (n : nat) (p : Parser A) : Parser (list A) :=
match n with
    | 0 => result []
    | S n' => plus
                (bind p (fun h =>
                 bind (many' n' p) (fun t =>
                   result (h :: t))))
                (result [])
end.

Open Scope char_scope.

Compute many' 5 letter "asdsd"%string.

Definition many {A : Type} (p : Parser A) : Parser (list A) :=
  fun input : string => many' (String.length input) p input.

Compute many digit "123"%string.

Definition fmap {A B : Type} (f : A -> B) (p : Parser A) : Parser B :=
  fun input : string =>
    map (fun p => (f (fst p), snd p)) (p input).

Fixpoint toString (l : list ascii) : string :=
match l with
    | [] => ""
    | c :: cs => String c (toString cs)
end.

Definition word' : Parser string :=
  fmap toString (many letter).

Compute word "abc"%string.
Compute word' "abc"%string.

Definition ident : Parser string :=
  bind lower (fun c =>
  bind (fmap toString (many alphanum)) (fun cs => result (String c cs))).

Compute ident "wut123"%string.

Definition many1 {A : Type} (p : Parser A) : Parser (list A) :=
  bind p (fun h =>
  bind (many p) (fun t =>
    result (h :: t))).

Compute many1 (char "a") "aaab"%string.

Fixpoint eval (cs : list ascii) : nat :=
match cs with
    | [] => 0
    | c :: cs' => nat_of_ascii c - 48 + 10 * eval cs'
end.

Definition parseNat : Parser nat :=
  fmap (fun l => eval (rev l)) (many1 digit).

Compute parseNat "123"%string.

Require Import ZArith.

Definition parseNeg : Parser nat :=
  fmap (fun l => eval (rev l))
    (bind (char "-") (fun _ => many1 digit)).

Definition parseZ : Parser Z :=
  plus
    (fmap Z_of_nat parseNat)
    (fmap (fun n => Z.sub 0%Z (Z_of_nat n)) parseNeg).

Compute parseZ "-12345"%string.

Definition parseSign : Parser (Z -> Z) :=
(*  fmap (fun l => match l with | [] => [] | h :: _ => [h] end)*)
    plus
      (bind (char "-") (fun _ =>
      (result (fun k => Z.sub 0%Z k))))
      (result id).

Definition parseZ' : Parser Z :=
  bind parseSign (fun f =>
  bind parseNat (fun n =>
    result (f (Z_of_nat n)))).

Compute parseZ' "-12345"%string.

(** *** 4.2 Repetition with separators *)

Definition sepby1 {A B : Type} (p : Parser A) (sep : Parser B) : 
  Parser (list A) :=
    bind p (fun h =>
    bind (many (bind sep (fun _ => p))) (fun t =>
      result (h :: t))).

Definition bracket {A B C : Type}
  (open : Parser A) (content : Parser B) (close : Parser C) : Parser B :=
    bind open (fun _ =>
    bind content (fun res =>
    bind close (fun _ =>
      result res))).

Definition ints : Parser (list Z) :=
  bracket (char "[") (sepby1 parseZ (char ",")) (char "]").

Compute ints "[1,2]"%string.

Definition sepby {A B : Type}
  (item : Parser A) (sep : Parser B) : Parser (list A) :=
    plus (sepby1 item sep) (result []).

(** *** 4.3 Repetition with meaningful separators *)

(**
    expr    ::= expr addop factor | factor
    addop   ::= + | -
    factor  ::= nat | ( expr )
*)

Fixpoint exprn (n : nat) : Parser Z :=
match n with
    | 0 => result 42%Z
    | S n' =>
        let
          addop := plus (bind (char "+") (fun _ => result Z.add))
                        (bind (char "-") (fun _ => result Z.sub))
        in let
          factor := plus parseZ
                         (bracket (char "(") (exprn n') (char ")"))
        in
          plus
            (bind (exprn n') (fun x =>
             bind addop (fun op =>
             bind factor (fun y =>
               result (op x y)))))
            factor
end.

Definition expr : Parser Z :=
  fun input : string => exprn (String.length input) input.

Compute expr "2+2"%string.

Compute expr "0-5)"%string.

Notation "a |: b" := (plus a b) (at level 50).

Definition chainl1
  {A : Type} (p : Parser A) (p_op : Parser (A -> A -> A)) : Parser A :=
    bind p (fun start =>
    bind (many (bind p_op (fun op =>
                bind p (fun arg =>
                  result (op, arg)))))
         (fun l => result (fold_left (fun x p => fst p x (snd p)) l start))).

Fixpoint exprn'' (n : nat) : Parser Z :=
match n with
    | 0 => result 0%Z
    | S n' =>
        let
          op := bind (char "+") (fun _ => result Z.add) |:
                bind (char "-") (fun _ => result Z.sub)
        in let
          factor := parseZ |: bracket (char "(") (exprn'' n') (char ")")
        in
          chainl1 factor op
end.

Definition expr'' : Parser Z :=
  fun input : string => exprn'' (String.length input) input.

Compute expr'' "3-2"%string.

Definition ops
  {A B : Type} (start : Parser A * B) (l : list (Parser A * B)) : Parser B :=
match l with
    | [] => let '(p, op) := start in bind p (fun _ => result op)
    | h :: t =>
        fold_right plus (bind (fst start) (fun _ => result (snd start)))
          (map (fun x => bind (fst x) (fun _ => result (snd x))) l)
end.

Fixpoint exprn3 (n : nat) : Parser Z :=
match n with
    | 0 => result 0%Z
    | S n' =>
        let
          op := ops (char "+", Z.add) [(char "-", Z.sub)]
        in let
          factor := parseZ |: bracket (char "(") (exprn3 n') (char ")")
        in
          chainl1 factor op
end.

Definition expr3 : Parser Z :=
  fun input : string => exprn3 (String.length input) input.

Compute expr'' "1-(2-(3-4)-5)"%string.

(* TODO: chainl1 alternative and chainr1 *)