(** The file won't compile. It's a snippet to be put into the thesis that
    lists (nearly) all the tactics used for automation. *)
Require Export Coq.Logic.FunctionalExtensionality.

Tactic Notation "ext" ident(x) := extensionality x.
Tactic Notation "ext2" ident(x) ident(y) := ext x; ext y.
Tactic Notation "ext3" ident(x) ident(y) ident(z) :=
  ext x; ext y; ext z.
Tactic Notation "ext" := let x := fresh "x" in ext x.
Ltac exts := repeat ext.

Ltac unmatch x :=
match x with
    | context [match ?y with _ => _ end] => unmatch y
    | _ => destruct x
end.

Ltac destr := repeat
match goal with
    | x : _ * _ |- _ => destruct x
    | x : _ + _ |- _ => destruct x
    | x : unit |- _ => destruct x
    | |- context [match ?x with _ => _ end] => unmatch x
end.

Ltac simplify :=
  cbn; intros; exts; destr.

Hint Rewrite @id_eq @id_left @id_right : CoqMTL.

Ltac hs :=
  cbn; intros;
  repeat (autorewrite with CoqMTL + autounfold with CoqMTL);
  try (unfold compose, id, const; congruence + reflexivity).

Ltac monad := repeat (simplify; try (hs; fail);
match goal with
    | |- ?x >>= _ = ?x =>
        rewrite <- bind_pure_r; f_equal
    | |- ?x = ?x >>= _ =>
        rewrite <- bind_pure_r at 1; f_equal
    | |- ?x >>= _ = ?x >>= _ => f_equal
    | _ => hs
end).