Load ast.

Definition programState : Type := (expression * instance * nat).

Fixpoint semantics (ps:programState) : programState :=
ps.
