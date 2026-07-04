From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.

Open Scope R_scope.

Theorem liouville_bound : forall c P : R,
  (c - 1) / 24 + P * P >= (c - 1) / 24.
Proof.
  intros c P.
  assert (H: P * P >= 0).
  { nra. }
  lra.
Qed.
