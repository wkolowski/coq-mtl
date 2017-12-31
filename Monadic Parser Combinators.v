(** * Monadic Parser Combinators *)

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

Fixpoint neWord : Parser string :=
  bind letter (fun h =>
  bind neWord (fun t =>
    result (String h t))).