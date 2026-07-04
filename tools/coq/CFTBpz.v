From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma central_charge_eq : forall b : R, b <> 0 ->
  1 + 6 * (b + 1/b) * (b + 1/b) = 13 + 6 * (b * b) + 6 / (b * b).
Proof.
  intros b Hb.
  field.
  exact Hb.
Qed.
