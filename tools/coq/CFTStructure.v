From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Lemma conformal_spin_sum : forall (S T n m : R),
  2 * S = n ->
  2 * T = m ->
  2 * (S + T) = n + m.
Proof.
  intros S T n m H1 H2.
  lra.
Qed.
