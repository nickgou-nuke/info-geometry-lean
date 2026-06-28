From Stdlib Require Import Reals Lra Field Psatz.

Open Scope R_scope.

Definition pellis_expr (phi : R) : R :=
  360 / (phi ^ 2) - 2 / (phi ^ 3) + 1 / ((3 * phi) ^ 5).

Definition pellis_normal_form (phi : R) : R :=
  176410 / 243 - (88447 / 243) * phi.

Lemma phi_nonzero : forall phi : R, phi^2 = phi + 1 -> phi <> 0.
Proof.
  intros phi h h0. rewrite h0 in h. lra.
Qed.

Theorem pellis_normal_form_theorem : forall phi : R,
  phi^2 = phi + 1 ->
  pellis_expr phi = pellis_normal_form phi.
Proof.
  intros phi hphi.
  assert (h0 : phi <> 0) by (apply phi_nonzero; exact hphi).
  assert (h1 : phi + 1 <> 0) by (intro hz; nra).
  assert (h3 : phi^3 = 2 * phi + 1).
  {
    replace (phi ^ 3) with (phi * phi^2) by ring.
    rewrite hphi.
    nra.
  }
  assert (h3nz : 2 * phi + 1 <> 0).
  {
    rewrite <- h3.
    apply pow_nonzero.
    exact h0.
  }
  assert (h5 : phi^5 = 5 * phi + 3).
  {
    replace (phi ^ 5) with (phi^2 * phi^3) by ring.
    rewrite hphi, h3.
    nra.
  }
  assert (h5nz : 5 * phi + 3 <> 0).
  {
    rewrite <- h5.
    apply pow_nonzero.
    exact h0.
  }
  assert (h_inv2 : / phi^2 = 2 - phi).
  {
    rewrite hphi.
    unfold Rdiv.
    apply Rmult_eq_reg_r with (phi + 1).
    - replace (/ (phi + 1) * (phi + 1)) with 1 by (symmetry; apply Rinv_l; exact h1).
      nra.
    - exact h1.
  }
  assert (h_inv3 : / phi^3 = 2 * phi - 3).
  {
    rewrite h3.
    unfold Rdiv.
    apply Rmult_eq_reg_r with (2 * phi + 1).
    - replace (/ (2 * phi + 1) * (2 * phi + 1)) with 1 by (symmetry; apply Rinv_l; exact h3nz).
      nra.
    - exact h3nz.
  }
  assert (h_inv5 : / (5 * phi + 3) = 5 * phi - 8).
  {
    apply Rmult_eq_reg_r with (5 * phi + 3).
    - replace (/ (5 * phi + 3) * (5 * phi + 3)) with 1 by (symmetry; apply Rinv_l; exact h5nz).
      nra.
    - exact h5nz.
  }
  assert (h31 : / ((3 * phi)^5) = (5 * phi - 8) / 243).
  {
    replace ((3 * phi) ^ 5) with (243 * phi^5) by ring.
    rewrite h5.
    unfold Rdiv.
    rewrite Rinv_mult.
    rewrite h_inv5.
    nra.
  }
  unfold pellis_expr, pellis_normal_form, Rdiv.
  rewrite h_inv2, h_inv3, h31.
  nra.
Qed.
