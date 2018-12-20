Class DoNotation (A B : Type) : Type :=
{
    do_bind : A;
    do_constrA : B;
}.

Notation "x >>= f" := (do_bind x f) (at level 40).

Notation "x '<-' e1 ; e2" := (do_bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).

(* TODO
Notation "x '<<--' e1 ;;; e2" := (bind e1 (fun y => let x := y in e2))
  (right associativity, at level 42, only parsing).
*)

Notation "e1 ;; e2" := (do_constrA e1 e2)
  (right associativity, at level 42, only parsing).

Notation "'do' e" := e (at level 50, only parsing).