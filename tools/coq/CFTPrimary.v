From Stdlib Require Import Reals.
Open Scope R_scope.

Section KacDimension.

Variables L1 Lm1 L0 : R -> R.
Variable V : R.

Hypothesis Lm1_linear_zero : Lm1 0 = 0.
Hypothesis commutator : L1 (Lm1 V) - Lm1 (L1 V) = 2 * (L0 V).
Hypothesis primary_state : L1 V = 0.

Theorem primary_eval : L1 (Lm1 V) = 2 * (L0 V).
Proof.
  rewrite primary_state in commutator.
  rewrite Lm1_linear_zero in commutator.
  assert (L1 (Lm1 V) - 0 = L1 (Lm1 V)) as H by ring.
  rewrite H in commutator.
  exact commutator.
Qed.

End KacDimension.
