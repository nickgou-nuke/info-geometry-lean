From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma hyperbolic_trace_bound : forall L : R, L <> 0 -> (L + 1/L)^2 - 4 = (L - 1/L)^2.
Proof.
  intros L HL.
  field.
  exact HL.
Qed.
