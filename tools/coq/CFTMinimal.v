From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Lemma boundary_constraint : 1 - 6 * (4 - 3)^2 / (4 * 3) = 1 / 2.
Proof.
  lra.
Qed.
