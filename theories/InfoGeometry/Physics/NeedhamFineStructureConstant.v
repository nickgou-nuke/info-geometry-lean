From Stdlib Require Import Reals Lra Field Psatz.

Open Scope R_scope.

Definition phi : R := (1 + sqrt 5) / 2.
Definition needham_alpha_inverse : R := 10 * PI * phi * exp 1 - ln PI.
Definition codata2018_alpha_inverse : R := 137.035999084.
Definition needham_abs_error : R := Rabs (needham_alpha_inverse - codata2018_alpha_inverse).
Definition needham_rel_error : R := needham_abs_error / codata2018_alpha_inverse.

Lemma phi_sq : phi ^ 2 = phi + 1.
Proof.
  unfold phi.
  assert (hs : (sqrt 5)^2 = 5).
  { replace ((sqrt 5)^2) with (sqrt 5 * sqrt 5) by ring.
    rewrite sqrt_sqrt; lra. }
  nra.
Qed.

Lemma phi_pos : 0 < phi.
Proof.
  unfold phi.
  assert (0 <= sqrt 5) by apply sqrt_pos.
  lra.
Qed.

Theorem needham_alpha_inverse_eq_closed_form :
  needham_alpha_inverse = 5 * PI * (1 + sqrt 5) * exp 1 - ln PI.
Proof.
  unfold needham_alpha_inverse, phi.
  field.
Qed.

Lemma codata2018_alpha_inverse_pos : 0 < codata2018_alpha_inverse.
Proof.
  unfold codata2018_alpha_inverse; lra.
Qed.

Lemma needham_abs_error_nonneg : 0 <= needham_abs_error.
Proof.
  unfold needham_abs_error.
  apply Rabs_pos.
Qed.

Lemma needham_rel_error_nonneg : 0 <= needham_rel_error.
Proof.
  unfold needham_rel_error, Rdiv.
  apply Rmult_le_pos.
  - apply needham_abs_error_nonneg.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    exact codata2018_alpha_inverse_pos.
Qed.
