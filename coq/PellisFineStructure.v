(*
  Pellis Fine-Structure Constant - Coq Formalization
  Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵
*)

Require Import Reals Lra sqrt.
Require Import Psatz.
Open Scope R.

Section PellisFineStructure.

(** Golden ratio definition *)
Definition phi : R := (1 + sqrt 5) / 2.

(** Positivity *)
Lemma phi_pos : phi > 0.
Proof.
  unfold phi.
  apply Rlt_div_r.
  - apply Rlt_0_1.
  - apply Rplus_lt_compat_r.
    apply sqrt_lt.
    + apply Rlt_0_1.
    + apply Rlt_pow_2.
      apply Rlt_0_1.
Qed.

Lemma phi_neq_zero : phi <> 0.
Proof. intro H; apply Rlt_irref with (r := 0); lra. Qed.

(** Quadratic relation: φ² = φ + 1 *)
Lemma phi_quadratic : phi * phi = phi + 1.
Proof.
  unfold phi.
  field_simp.
  replace (sqrt 5 * sqrt 5) with 5 by (symmetry; apply sqrt_square; lra).
  ring.
  lra.
Qed.

(** Inverse power: φ⁻² = 2 - φ *)
Lemma phi_inv_sq : / phi ^ 2 = 2 - phi.
Proof.
  replace (/ phi ^ 2) with (/ (phi + 1)) by (rewrite phi_quadratic; reflexivity).
  field_simp.
  replace (phi * phi) with (phi + 1) by apply phi_quadratic.
  ring.
Qed.

(** Inverse power: φ⁻³ = 2φ - 3 *)
Lemma phi_inv_cube : / phi ^ 3 = 2 * phi - 3.
Proof.
  assert (H3: phi ^ 3 = 2 * phi + 1).
  {
    calc phi ^ 3 = phi * phi ^ 2 : by ring
               _ = phi * (phi + 1) : by rw phi_quadratic
               _ = 2 * phi + 1 : by ring; rewrite phi_quadratic; ring.
  }
  rewrite H3.
  field_simp.
  ring.
Qed.

(** Inverse power: φ⁻⁵ = 5φ - 8 *)
Lemma phi_inv_fifth : / phi ^ 5 = 5 * phi - 8.
Proof.
  assert (H4: phi ^ 4 = 3 * phi + 2).
  {
    calc phi ^ 4 = phi * phi ^ 3 : by ring
               _ = phi * (2 * phi + 1) : by rewrite phi_inv_cube; field_simp; ring
               _ = 3 * phi + 2 : by ring; rewrite phi_quadratic; ring.
  }
  assert (H5: phi ^ 5 = 5 * phi + 3).
  {
    calc phi ^ 5 = phi * phi ^ 4 : by ring
               _ = phi * (3 * phi + 2) : by rewrite H4
               _ = 5 * phi + 3 : by ring; rewrite phi_quadratic; ring.
  }
  rewrite H5.
  field_simp.
  ring.
Qed.

(** Pellis formula *)
Definition pellis_alpha_inv : R :=
  360 / phi ^ 2 - 2 / phi ^ 3 + 1 / (3 * phi) ^ 5.

(** Normal form theorem *)
Theorem pellis_normal_form :
  pellis_alpha_inv = 176410 / 243 - 88447 / 243 * phi.
Proof.
  unfold pellis_alpha_inv.
  rewrite phi_inv_sq, phi_inv_cube, phi_inv_fifth.
  field_simp.
  ring.
Qed.

(** Bounds theorem: matches CODATA 2018 *)
Theorem pellis_bounds :
  1370359991 / 10000000 < pellis_alpha_inv /\
  pellis_alpha_inv < 171294999 / 1250000.
Proof.
  split.
  - (* Lower bound *)
    unfold pellis_alpha_inv, phi.
    assert (H: sqrt 5 > 2.236067977499789696).
    { apply Rsqrt_gt. lra. }
    lra.
  - (* Upper bound *)
    unfold pellis_alpha_inv, phi.
    assert (H: sqrt 5 < 2.236067977499789697).
    { apply Rsqr_lt_sqrt. lra. lra. }
    lra.
Qed.

(** CODATA agreement *)
Theorem codata_agreement :
  Rabs (pellis_alpha_inv - 137035999084 / 1000000000) < 1 / 10000000.
Proof.
  destruct pellis_bounds as [H1 H2].
  unfold Rabs.
  case (Rle_le 0 (pellis_alpha_inv - 137035999084 / 1000000000)); intro H.
  - lra.
  - lra.
Qed.

End PellisFineStructure.