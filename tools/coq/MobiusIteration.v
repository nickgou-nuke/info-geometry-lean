From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma mobius_iteration : forall L : R, L <> 0 -> (L^2 + (1/L)^2) = (L + 1/L)^2 - 2.
Proof.
  intros L HL.
  unfold Rminus.
  field.
  exact HL.
Qed.
