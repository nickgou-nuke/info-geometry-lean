import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.PellisGoldenAlpha

noncomputable section

/-- Pellis's golden-ratio ansatz for the inverse fine-structure constant. -/
def pellisExpr (φ : ℝ) : ℝ :=
  360 / φ^2 - 2 / φ^3 + 1 / (3 * φ)^5

/-- The exact linear normal form in the basis `{1, φ}`. -/
def pellisNormalForm (φ : ℝ) : ℝ :=
  (176410 : ℝ) / 243 - ((88447 : ℝ) / 243) * φ

lemma phi_ne_zero {φ : ℝ} (hφ : φ^2 = φ + 1) : φ ≠ 0 := by
  intro h0
  rw [h0] at hφ
  norm_num at hφ

/-- Under the quadratic relation `φ² = φ + 1`, Pellis's expression reduces to a linear form. -/
theorem pellis_normal_form {φ : ℝ} (hφ : φ^2 = φ + 1) :
    pellisExpr φ = pellisNormalForm φ := by
  have h0 : φ ≠ 0 := phi_ne_zero hφ
  have h3 : φ^3 = 2 * φ + 1 := by nlinarith [hφ]
  have h5 : φ^5 = 5 * φ + 3 := by nlinarith [hφ]
  have h_inv2 : 1 / φ^2 = 2 - φ := by
    field_simp [h0]
    nlinarith [hφ]
  have h_inv3 : 1 / φ^3 = 2 * φ - 3 := by
    field_simp [h0]
    nlinarith [h3]
  have h_inv5 : 1 / φ^5 = 5 * φ - 8 := by
    field_simp [h0]
    nlinarith [h5]
  rw [pellisExpr, pellisNormalForm]
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have hdiv2 : 360 / φ^2 = 360 * (2 - φ) := by
    rw [div_eq_mul_one_div, h_inv2]
  have hdiv3 : 2 / φ^3 = 2 * (2 * φ - 3) := by
    rw [div_eq_mul_one_div, h_inv3]
  have h31 : 1 / (3 * φ)^5 = (5 * φ - 8) / 243 := by
    have hpow : (3 * φ)^5 = 243 * φ^5 := by ring_nf
    rw [hpow]
    field_simp [h0, h3ne]
    nlinarith [h5]
  rw [hdiv2, hdiv3, h31]
  ring_nf

end
