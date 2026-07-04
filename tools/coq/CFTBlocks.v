From Stdlib Require Import Reals.
Open Scope R_scope.

Definition cross_ratio (z1 z2 z3 z4 : R) : R :=
  ((z1 - z3) * (z2 - z4)) / ((z1 - z4) * (z2 - z3)).

Lemma cross_ratio_translation : forall z1 z2 z3 z4 c : R,
  cross_ratio (z1 + c) (z2 + c) (z3 + c) (z4 + c) = cross_ratio z1 z2 z3 z4.
Proof.
  intros z1 z2 z3 z4 c.
  unfold cross_ratio.
  replace (z1 + c - (z3 + c)) with (z1 - z3) by ring.
  replace (z2 + c - (z4 + c)) with (z2 - z4) by ring.
  replace (z1 + c - (z4 + c)) with (z1 - z4) by ring.
  replace (z2 + c - (z3 + c)) with (z2 - z3) by ring.
  reflexivity.
Qed.
