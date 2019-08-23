Ltac inv H := inversion H; subst; clear H.

Require Export Coq.Logic.FunctionalExtensionality.

Ltac ext_aux x := extensionality x.

Tactic Notation "ext" ident(x) := extensionality x.
Tactic Notation "ext2" ident(x) ident(y) := ext x; ext y.
Tactic Notation "ext3" ident(x) ident(y) ident(z) := ext x; ext y; ext z.

Tactic Notation "ext" := let x := fresh "x" in ext x.
Ltac exts := repeat ext.

Hint Rewrite @id_eq @id_left @id_right : HSLib.

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

Ltac hs :=
  cbn; intros;
  repeat (autorewrite with HSLib + autounfold with HSLib);
  try (unfold compose, id, const; congruence + reflexivity).