From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma mobius_lorentz_det : forall x0 x1 x2 x3 : R,
  (x0 + x1) * (x0 - x1) - (x2^2 + x3^2) = x0^2 - x1^2 - x2^2 - x3^2.
Proof.
  intros.
  ring.
Qed.
