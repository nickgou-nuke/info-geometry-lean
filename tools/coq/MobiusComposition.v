From Stdlib Require Import Reals.
Open Scope R_scope.

Definition f1 (z c d : R) := z + d / c.
Definition f2 (z : R) := 1 / z.
Definition f3 (z a b c d : R) := ((b * c - a * d) / (c * c)) * z.
Definition f4 (z a c : R) := z + a / c.

Lemma mobius_composition : forall a b c d z : R,
  c <> 0 ->
  c * z + d <> 0 ->
  f4 (f3 (f2 (f1 z c d)) a b c d) a c = (a * z + b) / (c * z + d).
Proof.
  intros a b c d z Hc Hczd.
  unfold f1, f2, f3, f4.
  assert (z + d / c <> 0) as Hzdc.
  { intro H. apply Hczd.
    replace (c * z + d) with (c * (z + d / c)).
    - rewrite H. ring.
    - field. assumption. }
  field.
  repeat split; assumption.
Qed.
