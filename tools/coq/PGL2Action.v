From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma pgl2_fractional_mapping : forall a b c d z1 z2 : R,
  z2 <> 0 ->
  c * z1 + d * z2 <> 0 ->
  c * (z1 / z2) + d <> 0 ->
  (a * z1 + b * z2) / (c * z1 + d * z2) = (a * (z1 / z2) + b) / (c * (z1 / z2) + d).
Proof.
  intros a b c d z1 z2 Hz2 Hden1 Hden2.
  field; auto.
Qed.
