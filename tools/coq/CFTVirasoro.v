From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition C (m : Z) : Z := m * (m * m - 1).

Lemma C_antisym : forall m : Z, C m = - (C (-m)).
Proof.
  intro m.
  unfold C.
  ring.
Qed.
