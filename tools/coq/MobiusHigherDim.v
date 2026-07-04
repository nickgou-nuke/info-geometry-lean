From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Lemma reflection_involution_1D :
  forall x a r : R,
  a <> 0 ->
  let R_x := x - 2 * ((x * a - r)/(a * a)) * a in
  R_x - 2 * ((R_x * a - r)/(a * a)) * a = x.
Proof.
  intros x a r Ha R_x.
  unfold R_x.
  field.
  exact Ha.
Qed.
